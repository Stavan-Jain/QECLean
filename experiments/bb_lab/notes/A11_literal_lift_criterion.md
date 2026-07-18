# A11 — A checkable criterion for literal-lift doubling

**Status: Stage 0 (plan).** Branch `claude/a8-literal-lift-criterion`, cut from
the PR #53 head (`292a830`: parametric doubling layer + Z3Z6 instance + A9
screen). This file is the running log for the effort; results accrete below
the plan, A9/A10-style. Date: 2026-07-02.

Companions: `A8_doubling_extension_writeup.md` (the conjecture under test),
`A9_lean_target_screen.md` (the labeled instance pool),
`A10_descent_twist_screen.md` (the sibling *existence/twist* question —
see §9 for the division of labor), `docs/gross-distance-extensibility.md`
§3 (the doubling template the criterion must surrogate).

---

## 0. TL;DR

**Question.** Find a predicate `P(H, A, B, axis)` — computable from the base
presentation and the chosen cover axis *without ever solving the cover's
distance* — such that

    P(H, A, B, axis)  ⟹  d(literal axis-lift cover) = 2 · d(base),

and, stretch goal, the converse too. "Literal lift" = same polynomials on
the axis-doubled group (gross ← its base; all A9 ladder data).

**Standing candidate (A8 §0).** *Z₂²-frame anchorable (A5 gates: floor-bearing
frame + multiplicity-free disjoint difference sets + mirrored projections) +
`dim ker ∂₂ = 6` + the squaring identity `(1+x²)B² = 1+x⁶` ⟹ the x-cover
doubles.* Three supporting groups (gross; Z₆×Z₁₄ exact both axes; Z₆×Z₁₈ at
`d > 7`, full ladders pending), zero counterexamples.

**What the existing data already forces on any answer:**

1. **A8 cannot be the *equivalent* criterion** — doubling happens far outside
   its hypothesis class. The 152 A9 T1 pairs all double with
   `dim ker ∂₂ = 2`, and the Lean-proven Z3Z6 pair *fails* the cascade's
   difference-set gate (A9 docstring). Equivalence, if reachable at all,
   needs a criterion at the level of the template conditions, not the
   engine-class hypotheses.
2. **Frame + anchorability + k are not sufficient on their own for a given
   axis.** On the engine frame itself, hit3/4/6-y double to exact
   `[[144,12,12]]` while hit2-x/y and hit3-x stay at 6 and hit5-x reaches
   only 8 (A9 §T2) — six anchorable `[[72,12,6]]` codes, same frame, mixed
   verdicts *per axis*. Whatever discriminates must be axis-sensitive:
   A8's squaring-identity conjunct is exactly the axis-sensitive one, and
   nobody has yet checked whether it discriminates these hits. **That check
   is pure polynomial arithmetic — the sharpest cheap experiment in this
   plan (S1).** If some (hit, axis) satisfies all A8 hypotheses and fails to
   double, A8 is refuted on the spot; if the hypotheses split the hits
   exactly along the doubling verdicts, A8 gains six new in-frame instances.
3. **The template's safe-floor surrogate is not necessary.** A9 rows 112–152
   double even though their safe-class *base coset minima* are 6 < 8 = 2d
   (the sheet-overlap term `2|v₀ ∧ v₁|` rescues them). So the natural
   "layer-provable" predicate is sufficient-shaped, not necessary-shaped,
   and an equivalence hunt must model the overlap term.

**Decisive experiments.** (E1 = S1) A8 hypothesis audit on the six anchorable
Z₆×Z₆ codes × both axes against the known ladder verdicts — hours, no SAT.
(E2 = S3) the pending Z₆×Z₁₈ full ladders — the standing falsification probe.
(E3 = S2/S4) a feature matrix over *every* labeled instance (the ~640-candidate
A9 hunt stream, successes AND failures) + boolean criterion search + held-out
adversarial validation on fresh frames.

**Epistemic grade.** A screen + conjecture-hardening effort (A9/A10 grade).
SAT is discovery/validation only (A_HANDOFF §1); the deliverable is a
criterion *conjecture* with an explicit support/counterexample census, a
Lean-obligation reading of each conjunct (§5 of the plan), and — where the
criterion holds on a small frame — new instances pushed through the
parametric layer as machine-checked validation.

---

## 1. The question, precisely

Fix a base presentation `(H, A, B)`: `H = ℤ_ℓ × ℤ_m`, `A, B ∈ F₂[H]`
(weight-3 pairs throughout the current corpus), `d = d(BB(H, A, B))` known
exactly. Fix `axis ∈ {x, y}`; wlog x below. The **literal lift** is
`BB(G̃, A, B)` with `G̃ = ℤ_{2ℓ} × ℤ_m`, the same polynomial expressions read
in `F₂[G̃]`, deck `δ = x^ℓ`. The doubling event is `d(BB(G̃, A, B)) = 2d`
(with `k` preserved — record `k(cover)` always; a `k`-drifting cover is not
a doubling instance).

**Well-posedness note.** Doubling is *presentation-sensitive*: equivalent
`(A, B)` presentations of the same base code can have inequivalent literal
lifts (the A9 T2 lesson — anchorability itself is not Aut-invariant). But
the literal lift is a function of the presentation, and so is `P`. Both
sides of the desired implication live at presentation level, so the question
is well-posed with no orbit quantifier. (Contrast A10's Lemma L1, where the
descent space washes presentation out.) Corollary for evaluation discipline:
every predicate is evaluated **on the same presentation the ladder was run
on**; orbit-maximized variants (`presentation_anchorable`) are recorded as
separate features, never silently substituted.

**Admissible predicate budget ("checkable").** Three cost tiers, all
strictly cheaper than the cover distance and all polynomial or
fixed-parameter in `|H|`:

- **T-a (closed form):** polynomial/difference-set arithmetic on `(A, B)` —
  D1 Sidon, D2 disjointness, D3 coordinate separation, `is_frobenius_related`,
  mirrored projections, parity/augmentation facts, explicit polynomial
  identities.
- **T-b (linear algebra):** ranks and solves in `F₂[H]` or `F₂[G̃]` —
  `k(base)`, `k(cover)`, `dim ker ∂₂`, `μ(Ann A)`, `μ(Ann B)` (min weight in
  a nullspace basis — note: basis-min, cheap, vs true coset min), Smith/`im Δ`
  data, ideal-membership solves, `σ_*` on `H₁(cover)` (the R2 check below).
- **T-c (bounded enumeration):** fixed-weight sweeps whose exponent is a
  *criterion parameter*, not `n` — the light-boundary census at weight
  `≤ 2d−1`, base-coset minima over `2^{dim ker ∂₂}` Smith classes at small
  cell counts, tight-witness search at weight exactly `d`.

Excluded: any SAT/enumeration over the cover's logical space (that is the
quantity being predicted), and anything super-polynomial without a fixed
small parameter.

**The homotopy-certificate hierarchy (the axis-sensitive conjunct, made
precise).** Write `δ = x^ℓ`. Define, in decreasing strength and increasing
generality (each tier implies the next; all are T-a/T-b checkable):

- **R0-sq:** ∃ univariate `q(x)`: `q(x) · P² = 1 + δ` in `F₂[G̃]` for some
  `P ∈ {A, B}`. This is A8's "squaring identity" — gross:
  `(1+x²)B² = 1+x⁶`; Z₆×Z₁₄ y-cover: `(1+y²+y⁴+y⁸)A² = 1+y¹⁴`. The shape
  works when `P²` collapses to a univariate polynomial in the doubled
  variable (the untouched axis squares away).
- **R0:** `1 + δ ∈ (P)` for some `P ∈ {A, B}` — principal-ideal membership.
  The Z3Z6 pair's certificate `p·B = 1+x³` (weight-8 `p`) is R0 but not
  R0-sq.
- **R1:** `1 + δ ∈ (A, B) ⊆ F₂[G̃]` — the two-generator ideal membership,
  one F₂-linear solve `[M_A | M_B] q = 𝟙_{1+δ}` in the `2|G̃|`-dim algebra.
- **R-chain:** the Lean layer's exact hypothesis shape — additive
  `C : C₁ → C₂`, `E : C₀ → C₁` with `1 + σ = ∂₂∘C + E∘∂₁` on the basis
  (`BBDoubling.lean`, `deckTrivial_of_homotopy_certificate`; the `E∘∂₁`
  correction strictly generalizes R1). Existence is again an F₂-linear
  solve.
- **R2:** the property itself — `σ_* = id` on `H₁(cover)`, computed by
  linear algebra on the cover complex. No certificate, still T-b.

A9's `R` column is R2; its `sqIdeal(q1=0)` column is (roughly) R0 with
`P = B`. The A8 conjecture pins R0-sq. **Which tier is the "right" conjunct
is itself an S1/S2 output** — the first place the criterion can gain or lose
precision.

**The template reduction (why a criterion should exist at all).** The
extensibility doc §3 reduces literal-lift doubling to four layered
conditions: (1) free ℤ₂ cover — automatic for a literal axis lift;
(2) homotopy R — checkable, the hierarchy above; (3) both sector floors
≥ 2d — **the only genuinely uncheckable-looking piece**; (4) tight diagonal
lift — checkable at T-c given `d` (a weight-`d` base logical outside
`im Δ`). So the criterion hunt is, concretely: **find T-a/T-b/T-c surrogates
for condition 3** — the safe floor (Smith-class coset minima + overlap) and
the dangerous floor (light-stabilizer census + the `|b| + 2m(b) ≥ 2d`
rungs). A8's anchorability + `ker ∂₂` + squaring package is one candidate
surrogate; the S3.0 seam-support gate (below) is another, discovered the
hard way.

---

## 2. Known instances — the constraint table

Every row is a literal axis lift with an exact or partially-pinned verdict.
The criterion must be TRUE on every ✓ row it claims to cover and FALSE on
every ✗ row (sufficiency); an *equivalent* criterion must split the table
exactly.

| base | frame | kerd2 | axis | verdict | source |
|---|---|---|---|---|---|
| gross base `[[72,12,6]]` (A=x³+y+y², B=y³+x+x²) | Z₂²×Z₃² | 6 | x | ✓ d=12 | A3/A4 analytic |
| Z₆×Z₁₄ `[[168,12,6]]` (A=1+y+x³y³, B=1+x+x²y⁷) | Z₂²×(Z₃×Z₇) | 6 | x | ✓ d=12 | A8 |
| same | | 6 | y | ✓ d=12 | A8 |
| 6 clean Z₆×Z₁₈ bases (d(base)=6) | Z₂²×(Z₃×Z₉) | 6 | x | ◐ d>7, ladders pending | A8 §6.2 |
| hit3 (A=y³+x+x², B=y+xy²+x²) | Z₂²×Z₃² | ? | y | ✓ d=12 | A9 T2 |
| hit4 (B=y²+xy³+x²y), hit6 (B=xy+x²y²+x³) | Z₂²×Z₃² | ? | y | ✓ d=12 | A9 T2 addendum |
| **hit2** (B: pin in S0) | Z₂²×Z₃² | ? | x, y | **✗ d stays 6** | A9 T2 |
| **hit3** | Z₂²×Z₃² | ? | x | **✗ d stays 6** | A9 T2 |
| **hit5** (B: pin in S0) | Z₂²×Z₃² | ? | x | **✗ d=8** | A9 T2 addendum |
| hit5 | | ? | y | ? (JSON regen needed) | A10 §3 |
| Z3Z6 pair (A=x²+y+y³, B=1+x+y²) | Z₂×Z₃² | 2 | x (split-class deck (3,0)) | ✓ d=8, **Lean-proven** | PR #53 |
| 152 T1 pairs (Z₃×Z₄/Z₃×Z₅/Z₃×Z₆/Z₄×Z₆) | mixed | 2 | per row | ✓ 2d exact | A9 T1 |
| T1 hunt complement (~hundreds of candidates) | mixed | 2 | per row | ✗ (per-row d in JSONL) | A9 hunt stream |
| toric ℤ_L×ℤ_L (A=1+x, B=1+y) | — | — | either | ✗ d=L | symmetry |
| 12 Z₃×Z₆ d=6 bases | — | — | both | ✗ (no [[72,k,12]] pair in pool) | A9 caveats |

Facts already extractable from the ✓ rows of the A9 T1 table: `R` (=R2) = Y,
linchpin = Y, tight witness = Y, k preserved on **all 152**; safe-coset
minima ≥ 2d on rows 1–111 only; `sqIdeal(q1=0)` mixed (N on all Z₃×Z₅ rows —
so R0(B) is *not* necessary even within T1). The failures' feature values
are NOT yet computed (the profiler ran on successes) — S2 fixes that; the
necessity analysis is empty until it does.

Open cells that S0/S1 must fill: hit2/hit5 exact `B` polynomials
(`data/a9/t2_presentation_hits.json` was never committed — regenerate from
the corpus duckdb, shared obligation with A10 S0); `dim ker ∂₂` for all five
hits; hit5-y ladder.

---

## 3. Candidate criteria, ranked by prior

- **C-A8 (axis-generalized A8).** `anchorable(H, A, B)` (a5 gate:
  weight-3 both blocks, floor-bearing frame, (ii) mult-free + disjoint,
  (iii) mirrored projections, engine-grade (i) on Z₂² frames)
  ∧ `dim ker ∂₂ = 6` ∧ R0-sq on the chosen axis. Scope: the engine-class
  (k=12) family. Prior: high on its class (3 groups, 0 counterexamples),
  but S1 can kill it in an afternoon. Also test the R0/R1 relaxations of
  the third conjunct — A8 may survive only in a loosened form.
- **C-layer ("the parametric layer's obligations discharge").**
  k preserved (T-b) ∧ R-chain certificate exists (T-b) ∧ the single-shape
  dangerous rung is seam-compatible (the S3.0 gate: per light boundary
  class `b`, a preimage `f₀` whose lifted sheet-0 seam is supported inside
  `supp b` — T-c over the ≤ 2d−1 census) ∧ safe-class base coset minima
  ≥ 2d (T-c, small `dim ker ∂₂` only). Interpretation: **P = "the current
  Lean layer can prove the doubling by direct sweeps"** — a criterion whose
  truth is machine-certifiable per instance. Known gaps going in: rows
  112–152 (safe minima = 6) show it is not necessary; the S2 question is
  whether it is *sufficient* (any hunt failure satisfying it would be a
  layer-soundness alarm — expect zero).
- **C-learned.** Decision-tree / small-DNF search over the S2 feature
  matrix, distilled by hand into algebra, then adversarially validated on
  frames the search never saw (the D1∧D2 → +D3 → +¬Frobenius history —
  extensibility §6 — is the cautionary tale: every difference-set criterion
  looked sufficient until the frame widened; assume the same failure mode
  here until a held-out pass says otherwise).
- **Necessary-side observations** (for the equivalence stretch): candidates
  from the T1 table are R2, k-preservation, tight witness. Each gets tested
  against the *failure* stream in S2; any that survives (holds on all ✓,
  fails on all ✗) is a candidate biconditional conjunct. The overlap-term
  rescue of rows 112–152 says the safe-side necessary condition, if it
  exists, is about `|p(v)| + 2|v₀ ∧ v₁|`, not `|p(v)|` alone — the one place
  new mathematics (not just screening) may be needed.

---

## 4. The feature matrix (S2 columns)

Per (presentation, axis) — every column no-cover-SAT, tier annotated:

- frame data: 2-part shape, odd part, CRT component fields (T-a/T-b);
- `k(base)`, `k(cover)` via rank (T-b); `dim ker ∂₂` (T-b);
- `μ(Ann A)`, `μ(Ann B)` basis-minima, per side (T-b);
- difference-set predicates: D1, D2, D3, `is_frobenius_related`,
  `two_sided_hypothesis` (T-a; `bb_lab.diffset_predicates`);
- anchorability: raw `is_anchorable` on the pinned presentation AND
  orbit-level `presentation_anchorable` as a separate column (T-a/T-b);
- certificate tiers: R0-sq(A), R0-sq(B), R0(A), R0(B), R1, R-chain, R2 —
  seven booleans (T-b); linchpin `im p_* ⊆ ker τ_*` (T-b; implied by R2 via
  `τ∘p = 1+σ`, recorded independently as a sanity cross-check);
- census & rungs: light-boundary census size at ≤ 2d−1, seam-compatibility
  of the single-shape rung per class (S3.0 gate), worst-class slack (T-c);
- safe side: per-Smith-class base coset minima (T-c, feasible for
  `dim ker ∂₂ = 2` frames and, with the 63-class dispatch, marginal at 6 —
  record feasibility itself as data); `ker ∂₂` weight multiset + orbit count
  (T-b/T-c; A8 §4.1(†) suggests the *structure*, not just the dimension,
  carries signal);
- tight witness: existence of a weight-`d` base logical outside `im Δ`
  (T-c);
- label: `d(cover)` exact or bounded (SAT, discovery-only), `k(cover)`,
  doubling boolean.

Instance pool: the full A9 hunt stream (~640 candidates over five frames —
regenerate with the profiler extended to failures), the A5 instances
(Z₆×Z₁₄ both axes; the Z₆×Z₁₈ six; the Z₆×Z₆ hunt hits), the six T2
anchorable codes × both axes, toric L ∈ {3,4,5}, and the Z₃×Z₆ d=6
non-doubling pool. Rough size: 700–800 labeled rows, ~25 features.

---

## 5. Stages

### S0 — data recovery (shared with A10 S0; do once, point both efforts at it)

- `uv sync` the lab env in this worktree; duckdb lives only in the main
  checkout — use the a9 script's `--db ../../../experiments/bb_lab/data/bb_instances.duckdb`
  plumbing (read-only per lab rules).
- Regenerate `data/a9/t2_presentation_hits.json` (`a9_lean_target_screen.py
  t2 --db ...`): pins hit2/hit5 `(A, B)` exactly. Record them in §2 here
  AND hand them to A10 §3 (its S0 has the same item).
- Regenerate the T1 hunt stream (`hunt`, 30–90 min, background,
  JSONL-resumable) — needed because the failures' rows are the necessity
  data. Confirm the JSONL records failures with per-candidate `d(cover)`;
  if the current writer drops them, patch it first (small diff).
- Reproduce two spot baselines before quoting anything: the Z3Z6 pair
  x-ladder (d=8) and one T1 row.

### S1 — the A8 audit on the engine frame (the decisive cheap experiment)

For each of the six anchorable Z₆×Z₆ codes (gross + hit2..hit6) × both axes
(12 rows): evaluate every A8 conjunct — anchorability (pinned presentation),
`dim ker ∂₂`, and the full certificate hierarchy R0-sq/R0/R1/R-chain/R2 per
axis — and set against the known verdicts (§2). Pure T-a/T-b; no SAT beyond
what S0 already ran. Outcomes:

- **Some (hit, axis) satisfies all A8 hypotheses and does not double →
  A8 REFUTED.** First-class output (the Z₃×Z₅ / (C-iv) precedent): diff the
  feature vectors of the refuting instance against gross/Z₆×Z₁₄ to find the
  missing conjunct; the repaired conjecture becomes C-A8′.
- **The hypotheses split the 12 rows exactly along the verdicts → A8 gains
  six in-frame instances**, and the tier at which the split happens (R0-sq
  vs R0 vs R1 vs R2) is identified — that tier is the axis-sensitive
  conjunct going forward.
- **The hypotheses under-cover (fail on a doubling row, e.g. hit3-y) →**
  A8's sufficiency is untouched but its coverage shrinks; the loosened-tier
  variants say how far it can stretch without breaking.

Also in S1: state the **axis-generalized A8** cleanly (the y-axis statement
with `A` in the certificate role — A8 §4.1 y-cover paragraph is the
template) so that "the conjecture" is one presentation-symmetric sentence
before the falsification arm spends compute on it.

### S2 — feature matrix + criterion search

Build the §4 matrix over the §4 pool (extend `a9_lean_target_screen.py`'s
profiler or a new `scripts/a11_feature_matrix.py`; reuse
`bb_lab.{poly,linalg,checks,diffset_predicates}`; JSONL under `data/a11/`).
Then:

- evaluate C-A8 (+variants) and C-layer coverage/violation tables:
  sufficiency check = zero rows with P ∧ ¬doubling; coverage = fraction of
  doubling rows with P;
- necessity screen: which single features (and 2–3-conjunct combinations)
  are true on ALL doubling rows and false on ALL failures; C-learned only
  from what survives;
- freeze a **held-out set before looking**: at minimum the Z₆×Z₁₈ ladders
  (S3), one unscreened small frame (e.g. Z₅×Z₆ or Z₃×Z₇ if the hunt can
  reach it), and the hit5-y cell.

### S3 — the falsification arm (compute campaign, background)

1. **Z₆×Z₁₈ full ladders** — the A8 §6.2 debt. Six clean bases, x-covers at
   `n = 432`: UNSAT 8..11 then SAT@12. Cost is the real risk: the
   `n = 336` UNSAT≤11 took ~43 min, `n = 432` is untested, and the solver
   memory (UNSAT intractable ≥ 288 for the *augmented* safe-floor
   encodings) warns the plain ladders may still be hours per weight step.
   Design: fail-fast (any SAT ≤ 11 refutes A8 → jackpot, stop), sequential,
   JSONL-resumable, and accept partial verdicts (`d > 9` etc.) as evidence
   rows rather than stalling the plan. Where the y-axis hypotheses hold,
   queue the y-ladders behind the x-ladders at lower priority.
2. **Adversarial instance hunt** — the overfitting insurance. Extend
   `a5_cover_cascade.py --hunt-direct` beyond the card-120 cap (Z₆×Z₂₂,
   Z₁₀×Z₆-adjacent frames, whatever the cap admits next) hunting bases that
   satisfy whichever criterion survives S2, then fail-fast probe their
   covers at ≤ 2d−1. Remember the A8 lesson: structural gates over-produce
   (151k hits, whole frames k=0-degenerate) — `k > 0` + exact base SAT
   before anything counts as an instance.
3. Fill the two open T2 cells (hit5-y; any hit4/6-x not yet laddered) —
   cheap at n = 144, and they are held-out rows for S2.

### S4 — necessity / equivalence analysis

With failures profiled: characterize every non-doubling instance in feature
space. Deliverable is one of (a) an equivalence conjecture with 0/0
violations both directions on 700+ rows including held-out — only then
promote the "⟺" claim; (b) the honest fallback — a sufficiency conjecture
with maximal coverage plus a documented family of uncovered doubling
instances and the specific obstruction (expected: the safe-overlap rescue
rows). If (b), pose the overlap-term question precisely (min over the
`p(v) = w` slice of `|w| + 2|v₀ ∧ v₁|` as a base-side quantity — the
Entry-16-style reduction is already per-base) as the follow-on math target.

### S5 — Lean-facing packaging

- Map each surviving conjunct to its layer obligation:
  R-chain → `deckTrivial_of_homotopy_certificate`; seam-compatible rung →
  `dangerous_zero_rung`; safe coset minima → `safeFloor_of_seamCosetFloor`
  sweeps; assembly → `chain_distance_eq_double` / `pauli_distance_eq_double`.
  Deliverable: a short "criterion ⟹ layer-provable" note in this file, plus
  a table: which of the 152 T1 pairs the layer could certify TODAY (the
  all-green rows 1–111 modulo sweep size).
- Validate by instantiation: push 1–2 fresh all-green pairs (distinct frame
  from Z3Z6, e.g. a Z₃×Z₄ or Z₃×Z₅ row) through the layer end-to-end. This
  is the machine-checked form of "the criterion's conjuncts are exactly the
  provable obligations."
- **Out of scope:** a parametric Lean proof `P ⟹ d = 2d` — that is the
  engine parametrization (the hit3-y "second gross" target owns it).

### S6 — writeup + propagation

A8 note status update (survives/refuted/repaired + the new instance table);
extensibility doc §3/§6/§8 deltas; A_HANDOFF pointer block; research_log
entry; memory update; promote the surviving criterion into
`a5_cover_cascade.py` as the DOUBLE_CANDIDATE v2 gate (today's gate is
frame-shape only).

---

## 6. Outcome forks

- **F-refuted** (S1 hit audit or S3 ladders kill A8): the counterexample is
  a first-class output; the feature diff drives the repair; the repaired
  C-A8′ re-enters S3 with fresh held-out compute. History says this is the
  *likely* fork for any fixed hypothesis set (two difference-set criteria
  died exactly this way).
- **F-survives-and-splits** (A8 hypotheses discriminate all 12 S1 rows +
  Z₆×Z₁₈ confirms): A8 stands with ~10 supporting instances across 3–4
  groups; publish as the engine-class criterion; C-layer covers the
  small-frame class; the union is the two-tier deliverable.
- **F-equivalence** (some S4 candidate splits everything including
  held-out): the strongest outcome — a checkable characterization
  conjecture; immediately pose the parametric proof as the next moonshot.
- **F-diffuse** (no clean boolean structure): the negative result is still
  publishable content for the extensibility doc — "doubling is not
  low-complexity-predictable from the base presentation" with the feature
  matrix as evidence; the S4(b) overlap-term math question becomes the
  headline follow-on.

---

## 7. Risks and traps

1. **Presentation sensitivity** (A9 T2 lesson): evaluate every predicate on
   the pinned presentation; record orbit-level variants separately; never
   let a canonicalization step silently change the polynomials between the
   predicate and the ladder.
2. **Overfitting to screened frames** (the D1∧D2 → D3 → ¬Frobenius arc):
   no sufficiency claim without the held-out pass; the S3 adversarial hunt
   is mandatory, not optional.
3. **SAT epistemics** (A_HANDOFF §1): all distances are discovery/validation.
   The deliverable's claims are conjectures + Lean-certified instances;
   phrase every table accordingly.
4. **Solver asymmetry at n = 432**: UNSAT ladders may be hours per step;
   fail-fast design, partial verdicts recorded as `d > w`, never block the
   criterion work on ladder completion (they are held-out rows, not inputs).
5. **Hand-rolled encodings**: only `bb_lab.sat_distance` (validated); any
   new helper reproduces the S0 spot baselines before its output is quoted.
6. **k>0 flood** (A8 §1 lesson): structural hunts over-produce; `k > 0` +
   exact base distance before an instance enters any table.
7. **Compute hygiene**: SAT arm is lake-free (no workspace-lock contention);
   any S5 Lean builds run sequentially with other lake work; duckdb
   read-only; all outputs under `data/a11/` (JSONL, append-only, resumable);
   commit only small load-bearing artifacts.
8. **Coordination with A10**: shared S0 (do once); A10's twist screens on
   hit2/hit5 and this plan's S1 audit are complementary — if S1 shows A8's
   hypotheses already explain hit2/hit5's literal failures, A10 inherits a
   prediction (do twists that *restore* the certificate also restore
   doubling?). Run S1 before A10 S4 if scheduling allows.

---

## 8. Definition of done

- [ ] S0: hit2/hit5 polynomials pinned here + in A10; T1 hunt stream
      regenerated with failures; spot baselines reproduced.
- [ ] S1: 12-row A8 audit table in this file; verdict (refuted / splits /
      under-covers) + the discriminating certificate tier identified;
      axis-general A8 stated.
- [ ] S2: feature matrix over ≥ 700 rows committed (generator script +
      small JSONL); C-A8/C-layer coverage tables; necessity screen done;
      held-out set frozen and documented.
- [ ] S3: Z₆×Z₁₈ ladder verdicts (full or explicitly partial) recorded;
      ≥ 1 adversarial hunt round on a fresh frame; open T2 cells filled.
- [ ] S4: equivalence or sufficiency-with-gaps verdict, with the violation
      census; if gaps — the overlap-term question stated precisely.
- [ ] S5: criterion→layer obligation map written; 1–2 new instances proven
      through the layer as validation.
- [ ] S6: A8/extensibility/handoff/research-log/memory updates; cascade
      gate v2 if a criterion survived.

---

## 9. Relation to A10 (division of labor)

A10 asks the **existence** question over the descent space: *does every
certified base admit SOME free-ℤ₂ cover (twists allowed) that doubles?*
A11 asks the **characterization** question at the zero-twist point: *which
`(H, A, B, axis)` make the LITERAL lift double?* They share S0 data
recovery and the hit2/hit5 spotlight, and they trade outputs: A11's feature
matrix is the vocabulary for A10's Fork-R "selection rule" hunt (explicitly
anticipated there), while A10's twist screens supply A11's S4 with
controlled perturbation data (same base, 256 covers, which feature flips
track the verdict flips). Neither blocks the other; the one sequencing
preference is A11-S1 before A10-S4 (cheap, and it may hand A10 a testable
prediction).

---
---

# Results log

## Entry 1 — S0 + S1: the audit verdict is in, and A8 SURVIVES its
## sharpest test by *flipping the hit2/hit5 negatives* (2026-07-02)

Artifacts: `scripts/a11_s1_audit.py` (hits / audit / ladders / baseline),
`scripts/a11_s2_matrix.py`, `scripts/a11_s3_diagnose.py`;
data under `data/a11/` (presentation hits, 1164-cell audit, ladder JSONL,
S2 matrix) — regenerable, only the scripts + this note are committed.

### S0 — data recovery (all green)

- Both spot baselines PASS (Z3Z6 doc pair 4→8; A9 T1 row 12 4→8).
- **Presentation-anchorable census reproduced exactly**: 326 Z₆×Z₆
  `k>0, d≥6` corpus codes → **6 anchorable codes in 6 classes** (Aut×swap
  orbit search, ~3 s). hit3 = `9b9581f986a0d0ac` ✓ matches A9.
  Labels pinned by stored-form identity:
  hit1 = `5620b8e2c34acc75` (gross base), hit3 = `9b95…`,
  hit4 = `8b3f…`, hit6 = `7023…`; the remaining two disambiguated by
  their known x-ladder verdicts (below): **hit5 = `9706a4ea60d7e978`**
  (stored B = `y^5+x*y+x^2`), **hit2 = `98ff6753f866aba0`**
  (stored B = `1+x*y^5+x^2*y`).
- **Documentation correction discovered in passing**: the pairs the A9
  note quotes per hit (e.g. hit3 `B = y+x*y^2+x^2`) are the STORED
  corpus forms, and those are **not anchorable presentations** — their
  `B` is monomial in neither axis, so gate (iii) fails. The anchorable
  presentations are different orbit points (96 per class). The A9 T2
  ladders therefore measured the *stored* presentations' covers. This
  distinction turned out to be the whole story (below).
- T1 hunt stream regenerated: 638 candidate rows — 152 DOUBLES ✓ exact
  match to A9 — plus **465 labeled failures and 21 k-drift rows** (the
  failures were never profiled before; they are S2's necessity data).

### S1 — the audit (1164 cells) + decisive ladders

Feature battery per cell (certificate hierarchy + invariants), stored
form + all 96 anchorable presentations × both axes per class. Solver
controls: toric-x `R0_B` correctly False, toy membership False, gross
classic pin `A8exact_B` True + anchorable True.

**Uniform on the engine frame** (every one of the 1164 cells):
`dim ker ∂₂ = 6`, `R0_A = R0_B = Y` (1+δ lies in EACH principal ideal),
`sq2 = R1 = Y`, `R2 = Y` (σ_* = id), linchpin = Y, `k(cover) = 12`,
tight witness = Y, μ(Ann A) = μ(Ann B) = 6. So on this frame **the
entire certificate hierarchy (R0-sq through R2) is non-discriminating**
— template conditions 1, 2, 4 hold for every presentation and both
axes; only condition 3 (the floors) can separate doubling from not.
Moreover every class carries anchorable presentations with the LITERAL
gross identity `(1+t²)P² = 1+δ` on **both** axes — so the A8 hypothesis
package is satisfiable on every (class, axis), including all the cells
A9 recorded as non-doubling. Refutation or a spectacular flip were the
only options.

**Ladder verdicts (n = 144, exact SAT, pinned presentations):**

| cell | presentation | d(cover) | note |
|---|---|---|---|
| hit3:stored:x | A=`y³+x+x²`, B=`y+xy²+x²` | **6** | reproduces A9 |
| hit4:stored:x | stored | **6** | NEW cell |
| hit6:stored:x | stored | **6** | NEW cell |
| hit5:stored:x | stored | **8** | reproduces A9 (disambiguates hit5) |
| hit5:stored:y | stored | **6** | NEW — fills A10 §3's open cell |
| hit2:stored:x / :y | stored | **6 / 6** | reproduces A9 |
| **hit3:anch36:x** | A=`x³+x⁴+x⁵y³`, B=`xy+xy²+x⁴` (A8-exact on A) | **12** | **FLIP** |
| **hit5:anch36:x** | A=`x³+x⁴+x⁵y³`, B=`xy²+x⁴+x⁴y` (A8-exact) | **12** | **FLIP** |
| **hit2:anch0:x** | A=`1+x+x²y³`, B=`y²+x³+x³y` (A8-exact) | **12** | **FLIP** |

(hit4/hit6 x-side A8-cells + hit2/hit5 y-side A8-cells queued; every
completed A8-cell so far doubles.)

**Headline findings:**

1. **Literal-lift doubling is presentation-sensitive within the same
   (code, axis).** hit3's stored x-lift has d = 6; its equivalent
   anchorable presentation's x-lift has d = 12. First concrete same-axis
   witness (A9 §caveats had anticipated the possibility abstractly).
2. **A8 survives and strengthens**: on every cell where its hypotheses
   hold and a ladder has completed, the cover doubles — including three
   cells where the stored-form verdict said "no doubling". The conjecture
   now has gross + Z₆×Z₁₄ + (Z₆×Z₁₈ partial) + **hit2/hit3/hit5
   anchorable x-cells** in support, zero counterexamples.
3. **A9's T2 negatives dissolve**: "hit2 and hit5 do not double" was an
   artifact of laddering the stored presentations. As *classes*, all six
   anchorable Z₆×Z₆ codes are gross-twins (doubling literal covers
   exist). A9's §T2, the extensibility doc §6/§7 ("hit2 and hit5 do not
   double"), and A10's §0/§3 premise ("known false at literal lifts —
   hit2/hit5 fail on both axes") all need corrections: A10's decisive
   Fork-C candidates are gone (its existence question is answered
   POSITIVELY for hit2/hit5 by literal lifts of equivalent
   presentations — no twists needed).
4. **Mechanism of the flip (diagnose tool)**: every non-doubling stored
   cell breaks in the SAFE sector — the min-weight cover logical
   projects to a nontrivial base logical whose safe-class coset min
   equals d(cover) exactly (6 or 8); the dangerous |b|+2m(b) rung never
   breaks on this frame. The flip is entirely a safe-floor phenomenon:
   equivalent presentations re-route `im p_*` through different
   base-logical classes.

### S2 — first matrix cuts (638-row hunt stream; job completing)

On the ~450 rows finished at first cut (94 DOUBLES / 348 shorts among
usable rows):

- `R1`, `R2`, linchpin: **true on 100% of BOTH classes**. *(Explained by
  a THEOREM the same day — A12 session, `A12_deck_homotopy_R.md` §3:
  for every free-ℤ₂ BB cover, `(R) ⟺ k(cover) = k(base) ⟺ R1
  [1+δ ∈ (A,B)]`; proof via Frobenius duality + the transfer-LES
  inequality + the Koszul reading of my one-line R1 ⟹ (R) mechanism.
  The hunt's DOUBLES/short rows are k-gated, so 100%-both-classes is
  FORCED: (R) can never discriminate within a k-preserving family.
  Scope caveat for any write-up: this is a k-gate fact, NOT a class
  fact — A12's ~1.04M-pair sweep found 11,307 (R)-violations, all
  k-jumping as the theorem forces, including strict-IBM-shape pairs on
  Z₆×Z₆ itself; and (R) is lift-dependent. My R0 observation — 1+δ in
  EACH principal ideal on the engine frame — is strictly stronger than
  R1 and matches the P=0 shape of both proven instance witnesses.)*
- **`safe_floor_ok` is sufficient-shaped with 0/348 violations**,
  covering 53/94 DOUBLES (the uncovered 41 = the overlap-rescue class,
  matching the A9 rows-112–152 observation exactly).
- **`tight_witness` is necessary** (94/94) but far from sufficient
  (54% of shorts have it).
- A8-exact/R0-sq: ~20% of doubles, ~9% of shorts — scope-limited to the
  engine class, as the plan predicted.
- D1/D2/D3/Frobenius: uncorrelated with doubling (they are base-floor
  predicates, not doubling predicates).

### Emerging synthesis (criterion shape after one day)

- The discriminating content of literal-lift doubling sits in **template
  condition 3's safe half** — checkable base-side (no cover SAT) as
  per-class coset minima: T-c sweeps at ≤ 24 cells, SAT-assisted coset
  ladders at 36 cells (`a11_s3_diagnose.py safefloor`), the (M-im)
  engine at proof grade.
- Candidate unified criterion (to harden in S3/S4):
  **C-safe := tight witness ∧ all safe-class coset minima ≥ 2d**
  (with R2/R1 riding along ~free). Sufficient with zero violations on
  everything measured so far; NOT necessary (the 41 overlap-rescued
  doubles) — the S4(b) overlap question stands.
- **A8's role sharpens**: on the engine frame its
  anchorable-presentation + squaring-identity package empirically
  selects presentations whose safe floor clears 2d — i.e. A8 is a
  checkable *proxy* for C-safe where C-safe's sweep is infeasible. Why
  anchorability re-routes the safe classes away from light logicals is
  now THE mechanism question (S4).

### Safe-floor probe scoreboard + REGISTERED PREDICTIONS

Base-side probes (`a11_s3_diagnose.py safefloor`, coset-min ladders at
n = 72, cap 11 — no cover SAT), against known cover verdicts:

| cell | safe-floor histogram | floor ok | d(cover) |
|---|---|---|---|
| hit3:stored:x | {6:12, 8:45, ≥12:6} | ✗ | 6 ✓ |
| hit3:anch36:x | {≥12: 63} | ✓ | 12 ✓ |
| hit3:stored:y | {≥12: 63} | ✓ | 12 ✓ (A9) |
| Z3Z6 doc pair (probe mode, cap 7) | {≥8: 3} | ✓ | 8 ✓ (Lean) |

**Predictions registered 2026-07-02 BEFORE the SAT verdicts** (ladders
still running at registration; probe result in
`data/a11/safefloor_predictions.log`, commit `8a6a06d`):

| cell | probe | prediction |
|---|---|---|
| hit5:anch40:y | {≥12: 63} | **d = 12** |
| hit2:anch16:y | {≥12: 63} | **d = 12** |
| hit4:anch48:x | {≥12: 63} | **d = 12** |
| hit6:anch24:x | {≥12: 63} | **d = 12** |

If confirmed, C-safe passes its first *prospective* test and the
engine-frame scoreboard is doubling ⟺ safe-floor on every tested cell
(the small-frame overlap-rescue rows keep the ⟸ direction one-way
globally; the reachable-coset refinement is the S4 candidate fix).

**ALL FOUR PREDICTIONS CONFIRMED (4/4)**: hit5:anch40:y → 12 (1021s),
hit2:anch16:y → 12 (1496s), hit4:anch48:x → 12 (167s),
hit6:anch24:x → 12 (298s). Full ladder scoreboard for the session —
7 stored cells all non-doubling (6/6/6/8/6/6/6), **7 anchorable
A8-package cells all d = 12 exactly**. Combined with A9's stored-y
ladders and gross: **every one of the six engine-frame classes doubles
on BOTH axes via its anchorable presentations**, and the base-side
safe-floor probe called every verdict it was asked to predict. On the
engine frame the tested scoreboard is exactly

    doubling  ⟺  safe_floor_ok      (per presentation and axis),

and A8's full package (anchorable + kerd2 6 + squaring identity) has
gone 7-for-7 on fresh SAT ladders with zero counterexamples anywhere.

### S2 final numbers (complete 638-row matrix; `a11_s2_analyze.py`)

152 DOUBLES + 465 shorts + 21 k-drift, 0 errors. Necessity/sufficiency
screen (P(f | DOUBLES) vs P(f | short)):

- **`safe_floor_ok`: 0.730 vs 0.000 — SUFFICIENT with 0/465 violations,
  covering 111/152** (C-safe adds nothing beyond it on this data — R2,
  linchpin, R1 are true on 100% of BOTH classes; `tight_witness` is
  implied wherever the floor holds).
- **`tight_witness`: 1.000 vs 0.482 — NECESSARY**, far from sufficient.
- **A8-exact / R0-sq: 0.507 vs 0.133 — enriched but NOT sufficient on
  the small frames (62 violating shorts)**. This sharpens A8's reading:
  the squaring identity alone provably does not buy doubling; the
  anchorability + engine-frame (kerd2 = 6) hypotheses are load-bearing.
  (On the engine frame, every A8-package cell laddered so far doubles.)
- Difference-set predicates (D1/D2/D3/Frobenius): uncorrelated, as
  expected — they govern the base floor, not the doubling.
- Per-frame C-safe coverage of DOUBLES: Z₃×Z₆:x 20/20, Z₄×Z₆:y 58/58,
  Z₃×Z₆:y 22/31, Z₃×Z₅:x 8/25, Z₃×Z₅:y 3/8, **Z₃×Z₄:y 0/10** — whole
  frames double exclusively through the overlap mechanism, others
  exclusively through heavy safe floors. The two mechanisms are both
  real and frame-correlated.

### S4 first cut — the reachable-coset refinement FAILS (dead end, first-class)

Hypothesis: the 41 overlap-rescue rows (DOUBLES with a safe-class base
coset min < 2d; frames Z₃×Z₅:x ×17, Z₃×Z₄:y ×10, Z₃×Z₆:y ×9, Z₃×Z₅:y ×5)
are explained by restricting each class coset to its *reachable* part
`rep + (rowspace(H_Z^base) ∩ p(cycle space))` — maybe the light coset
elements simply aren't projections. **Refuted**: `a11_s4_reachable.py`
computes the reachable minima exactly (subspace-intersection dual +
coset-min SAT) and gets **0/41 all-heavy** — e.g. reachable minima
`[6,6,6]` on rows whose covers still double to 8. So light projections
DO exist; every cover cycle over them just carries overlap
`|v| = |p(v)| + 2|v₀ ∧ v₁| ≥ 2d`. The necessity gap is genuine
slice-level mathematics — the safe-sector analogue of gross's m(b)
machinery (A_HANDOFF §4 Entry-16 anticipated the shape) — not an
accounting artifact. C-safe stays sufficient-only; the S4(b) question
is now precisely: *bound `min_{p(v)=w} |w| + 2|v₀ ∧ v₁|` from base data
on the light reachable classes.*

## Entry 2 — proof attempt: does the nonzero-b dangerous rung follow
## from C-safe's hypotheses? (2026-07-02)

**Verdict up front: NOT proven in general — but the attempt yields a
machine-validated structural collapse of the dangerous sector, three
unconditional rung pieces, an exact characterization of the irreducible
residue, and an upgraded criterion that IS provably sufficient with
every conjunct base-side-checkable.** Validation:
`scripts/a11_s4_dangerous_reduction.py` (V1–V5, 10/10 PASS on the Z3Z6
pair and hit3-stored; A_HANDOFF §4 discipline).

### Setup

Fix one CSS complex per side (stated for the primal/Z side; everything
dualizes). Base `C₂ →^{∂₂} C₁ →^{∂₁} C₀` over `F₂[H]`; cover over `G̃`
(axis-doubled), deck `σ`. A fundamental domain splits every monomial
action into cut-preserving and cut-crossing parts, giving `∂ = ∂ⁿᶜ + ∂ᶜ`
on the base and the block form `∂^cov = [[∂ⁿᶜ, ∂ᶜ],[∂ᶜ, ∂ⁿᶜ]]` in sheet
coordinates (V1). `τ(u) = (u,u)`, `p(v₀,v₁) = v₀+v₁`; SES of complexes;
`|v| = |p(v)| + 2|v₀ ∧ v₁|`.

**Lemma 1 (free, LES).** `ker p_* = im τ_*` and `ker τ_* = im Δ` on H₁,
with the connecting map's chain formula `Δ[ζ] = [∂₂ᶜ ζ]` and
`∂₂ᶜ ζ = ∂₂ⁿᶜ ζ` for `ζ ∈ ker ∂₂` (the lift `(ζ,0)` has diagonal
boundary; V2).

### Proposition D1 (dangerous collapse — the main structural find)

Every dangerous cover cycle (`p(v) = b ∈ Stab`) with `[v] ≠ 0`
decomposes as

    v = τ(ρ) + ∂₂^cov(y, 0),    ∂₂ y = b,
    sheets: v = (ρ + ∂₂ⁿᶜ y,  ρ + ∂₂ᶜ y),

with `[v] = τ_*[ρ]`. *Proof:* `[v] ∈ im τ_*` (Lemma 1) gives
`v = τ(x) + ∂₂^cov(Z₀, Z₁)`; since `∂₂^cov(Z₁,Z₁) = τ(∂₂ Z₁)`, absorb
the diagonal part: `v = τ(x + ∂₂Z₁) + ∂₂^cov(Z₀+Z₁, 0)`. ∎ (V3
validates forward on 50 random `(ρ,y)` per frame; V4 back-decomposes
real SAT minima.)

Moreover the residual freedom collapses: replacing `y ↦ y + ζ`
(`ζ ∈ ker ∂₂`) shifts the sheet pair by exactly `τ(∂₂ᶜ ζ)` (V5), i.e.
moves `[ρ]` through the **τ-fiber** `[u] + im Δ`. Hence for ONE fixed
preimage `y_b` of `b`:

    slice-min(b, τ_*[u]) = min over reps ρ of classes in [u]+im Δ of
                           |ρ + ∂₂ⁿᶜ y_b| + |ρ + ∂₂ᶜ y_b|.

**Corollary: the dangerous sector is a base-side quantity** — no cover
enumeration; a base-dimension optimization (SAT-able) per light `b`.

### Proposition D2 (unconditional rung pieces)

1. **b = 0**: the slice equals `2·min` over the *whole fiber* of class
   coset minima `≥ 2·d(base)` — free, since `0 ∉` fiber (else `[v] = 0`).
2. **|b| ≥ 2d**: free, `|v| ≥ |p(v)| = |b|`.
3. **Seam-trivial b** (some preimage with `∂₂ᶜ y_b = 0`): slice
   `= min_ρ |ρ| + |ρ + b| ≥ d + d` (both are reps of one nontrivial
   fiber class). Soft general bound: slice(b) `≥ 2d − |b| − 2|h ∧ h′|`
   for `h = ∂₂ᶜ y_b`, `h′ = ∂₂ⁿᶜ y_b`.

So the entire gap is: **stabilizers with `0 < |b| < 2d` whose every
preimage carries overlapping seam-halves that cancel against a τ-fiber
logical** — light, seam-flux-carrying stabilizers. (Under gross's
no-double-wrap identities and `∂₁ᶜ b = 0` one can push further: the
slice classes shift by the flux class `δ_b = [∂₂ᶜ y_b]` and the rung is
again free unless `δ_b` lands in the fiber — the residue is precisely
*flux-anomalous* light stabilizers.)

### Theorem (upgraded provable criterion — all conjuncts base-side)

    tight witness
    ∧  every nonzero im p_* class has base coset min ≥ 2d       (C-safe)
    ∧  every stabilizer b with 0 < |b| < 2d has slice-min ≥ 2d
       (computed via Prop D1's base-side formula)               (C-danger)
    ⟹  d(cover) = 2·d(base).

*Proof:* sector exhaustion. Safe classes by C-safe (`|v| ≥ |p(v)| ≥`
class min); dangerous `b = 0` by D2.1; `|b| ≥ 2d` by D2.2; light `b` by
C-danger; `≤ 2d` by the witness. ∎  This replaces the Lean layer's
cover-side safe/dangerous sweep obligations with base-side ones — the
practical S5 payoff of the attempt.

### Why C-safe alone resisted (the obstruction)

C-safe's floor constrains the **im Δ classes**; the dangerous slices
live on the **τ-fiber = the complement side** of H₁(base). The
hypotheses act on complementary halves, and no soft argument transfers
weight control across (`|ρ + h| ≥ |ρ| − |h|` is the best generic bound,
and the cancellation `|ρ ∧ h|` is exactly the quantity gross's m(b)
machinery exists to control). A principled reason to expect no soft
proof: it would derive gross's Theorem C from (M-im) + Theorem A +
duality — collapsing a major, twice-adversarially-reviewed component of
A4 that the program never found collapsible; and gross's own `b ≠ 0`
dangerous minimum is 14, not 12 — its truth is not forced by the floor
value. Status of "C-safe ⟹ light-b rung": exactly equivalent to C-safe
sufficiency; empirical record 0 violations on ~1000 cells; the
falsification target is now sharp — *construct* a light stabilizer with
deep seam-half cancellation against a min-weight fiber logical.

### Entry 2b — continuation: the shadow bound, the flux dichotomy, and
### the twice-refined residue (2026-07-02)

Three further propositions, each proven from the D1 collapse and
machine-validated (V6: 20k-random-triple check of the D4 algebra; V7:
end-to-end D7 mechanics on hit3-stored — see below).

**Prop D4 (seam-shadow bound).** Fix a light `b`, any preimage `y_b`,
`h = ∂₂ᶜy_b`, `h' = ∂₂ⁿᶜy_b`, and the seam shadow
`Σ(b) := supp(h) ∪ supp(h')`. Splitting any `ρ` into its parts inside
and outside `Σ` (and using that `h, h'` live inside `Σ`):

    |ρ + h| + |ρ + h'| = 2|ρ ∖ Σ| + |ρ_Σ + h| + |ρ_Σ + h'|
                       ≥ 2|ρ ∖ Σ| + |b|,

hence  **slice-min(b) ≥ |b| + 2·min over fiber reps ρ of |ρ ∖ Σ(b)|**
(and one may maximize the bound over preimages, and over cut positions
— every cut gives a valid bound).

**Prop D5 (concentration criterion).** The rung over `b` holds whenever
every representative of every τ-fiber class keeps at least
`d − |b|/2` weight outside `Σ(b)`. This is a **concentration bound for
logicals on small shapes** — precisely the statement family gross's
m-rungs instantiate: for a hexagon (`|b| = 6`, `2d = 12`) it demands
punctured weight ≥ 3, cf. gross's `m(hexagon) ≥ 3` ("no non-imΔ cycle
with ≤ 2 qubits off the hexagon"; gross punctures at `supp(b)`, we at
`Σ(b)` — same shape, and gross's mod-b coset-averaging is a proof
technique for exactly this kind of bound).

**Prop D6 (cheap per-instance check).** `min_ρ |ρ ∖ Σ(b)|` over a class
coset is the Σ-punctured coset minimum — the same dual-constraint SAT
as `coset_min` with the cardinality restricted to the complement of
`Σ`. So D5 is a *cheaper* sufficient sub-check for C-danger than the
full slice optimization.

**Prop D7 (trivial-flux rung).** Suppose some preimage's seam-half `h`
is a base cycle (`∂₁h = 0`) with `[h] ∈ im Δ`. Choosing `ζ ∈ ker ∂₂`
with `Δ[ζ] = [h]` and replacing `y_b ↦ y_b + ζ` makes the new `h` a
STABILIZER; then `ρ + h` and `ρ + h' = ρ + h + b` are both
representatives of the same nontrivial fiber class, so
`slice(b) ≥ d + d = 2d`. **The rung is free whenever the flux
`φ(b) := [∂₂ᶜ y_b] mod im Δ` is defined and vanishes** (the ζ-freedom
shifts the flux by exactly `im Δ`, so `φ(b) ∈ H₁(base)/im Δ ≅ im τ_*`
is canonical; it is the class of the one-sheet lift where that is a
cycle).

*Validation (V7, hit3-stored x):* of the 36 stabilizer generators, 24
have cycle seam-halves, **all 24 with trivial flux**, and the
ζ-replacement lands a stabilizer `h₂` in every case — D7 disposes of
all 24 of those generator rungs outright; the remaining 12 have
non-cycle seam-halves and fall to D4/D5 or per-instance work.

**The twice-refined residue.** Combining D2, D4–D7, the unproven
content of "C-safe ⟹ doubling" is now confined to stabilizers `b`
with ALL of: `0 < |b| < 2d`; no seam-trivial preimage; no
trivial-flux cycle seam-half (for any cut); and a τ-fiber logical
concentrating more than `d − |b|/2` inside the (best) seam shadow
`Σ(b)`. Everything else is theorem. A counterexample hunt targeting
exactly this cell is running (subagent, `scripts/a11_cx_*`,
`data/a11/cx/`); a proof of the concentration bound for the anchorable
class via the A5 difference-set machinery is the complementary route
(the "A8 proxy → theorem" path).

### Honesty ledger (tooling corrections found during validation)

`x_distance` witnesses are X-type operators (`ker H_Z`), so sector
diagnosis must run on the dual complex; the diagnose tool previously
tested `p(v)` against the Z-side stabilizer rowspace unconditionally.
Fixed side-aware (`a11_s3_diagnose.py`), all seven non-doubling stored
cells re-diagnosed: **every one still breaks in the SAFE sector, now
verified on the correct complex** (and on both complexes where the
witness lies in both kernels; X-coset min = Z-coset min = d(cover) on
each). The safe-floor probe and its 4/4 predictions were unaffected
(fully primal-side construction). The V4c failure that exposed the bug
is exactly why the validation-first discipline exists.

---

### Session close — state and next queue (2026-07-02)

**Criterion status after one session.** Two-tier answer to the A11
question, both empirical (SAT = discovery-grade; A_HANDOFF §1):

- **C-safe (frame-agnostic, sufficient):** k(cover) = k(base) — one rank
  computation, and by the A12 theorem EQUIVALENT to (R)/R1, so the
  homotopy conjunct is subsumed — ∧ tight witness ∧ every safe class
  coset min ≥ 2d. Zero violations across 465 small-frame failures +
  every engine-frame cell; covers 111/152 small-frame doubles and
  (scoreboard ⟺) all engine-frame cells tested. Checkable with NO cover
  SAT: T-c span sweeps at ≤ 24 cells, base-side SAT coset ladders at
  36+ cells (`a11_s3_diagnose.py`), 4/4 prospective predictions.
- **A8 (engine-frame proxy, sufficient):** anchorable presentation +
  `dim ker ∂₂ = 6` + squaring identity. 7/7 on fresh ladders (flipping
  every A9 stored-form negative), plus gross, Z₆×Z₁₄ ×2, Z₆×Z₁₈ (d>7
  partial). The identity ALONE is refuted as sufficient (62 small-frame
  shorts) — the frame/anchorability hypotheses are load-bearing.
- **Not equivalent** (both are sufficient-only): the 41 overlap-rescue
  rows — including the entire Z₃×Z₄:y doubling family — double with
  broken safe floors; the reachable-coset repair is refuted (0/41).

**Epistemic status of C-safe — NOT a theorem; the precise gap.**
Decompose a cover logical by its projection. What C-safe *provably*
delivers: the safe sector (`[p(v)] ≠ 0`) clears 2d (`|v| ≥ |p(v)| ≥`
class coset min, over exactly the `im p_*` classes the probe measures);
the `b = 0` dangerous rung is free (`p(v) = 0 ⟹ v = τ(w)`, `w` a
nontrivial base logical, `|v| = 2|w| ≥ 2d`); and the tight witness
caps `d(cover) ≤ 2d`. What it does NOT cover: the **nonzero-`b`
dangerous sector** — `p(v) = b ∈ Stab_Z ∖ 0`, where
`|v| = |b| + 2m(b)` and the rung `≥ 2d` is per-instance work (gross's
Prop 10 + (M); the layer's `dangerous_zero_rung`/single-shape rungs).
So "C-safe ⟹ doubling" is a CONJECTURE (0 violations on 465 + 492
cells + engine frame, 4/4 prospective; SAT-grade labels throughout);
the provable-today variant is C-safe ∧ the dangerous-rung obligations
= the Lean layer's full obligation set. The theorem-shaped open
question the data poses: every observed doubling failure, on every
frame, breaks in the SAFE sector — the nonzero-`b` rung has never been
seen to bind below 2d. Prove that under C-safe's hypotheses (or find
the cheap extra conjunct, e.g. the S3.0 seam-compatibility census, that
makes it provable) and C-safe becomes a theorem; gross's own `b ≠ 0`
dangerous minimum of 14 (cleared by 2, not by structural slack) says
this will not be free. And note the probe itself is SAT-assisted:
per-instance PROOF of the safe conjunct is the sweep/engine discharge
(S5), separate from the criterion's own conjectural status.

**Next-session queue, in order:**

1. **Z₆×Z₁₈ arm, probe-first redesign (S3).** Regenerate the anchorable
   candidates (`a5_cover_cascade.py --hunt-direct`, Z₆×Z₁₈ slice), dedup,
   `d(base) = 6` validation; then `a11_s3_diagnose.py probe` per
   candidate × axis (n = 216 base-side, cap 11) and REGISTER predictions;
   only then spend the n = 432 cover ladders, cheapest-first. This both
   settles A8's pending falsification probe and tests C-safe
   out-of-frame prospectively.
2. **S4 mechanism questions** (the real math): (a) WHY do anchorable +
   squaring-identity presentations select all-heavy Smith subgroups
   `im Δ` on the engine frame? (The A5/A8 machinery — mirrored
   projections pinning the seam — is the natural suspect; a proof here
   turns A8 from proxy into theorem-modulo-C-safe.) (b) the overlap
   slice bound `min_{p(v)=w} |w| + 2|v₀∧v₁| ≥ 2d` on light reachable
   classes — the missing necessity half; Z₃×Z₄:y (10 rows, 24-cell
   frames, fully overlap-carried) is the model system.
3. **S5 Lean packaging.** The 111 C-safe-covered pairs are exactly the
   layer-provable ones (safe floor by per-class sweeps at ≤ 2¹⁸ ×
   dispatch 4); pick 1–2 fresh-frame instances (a Z₄×Z₆:y row for a new
   frame) and push through `BBCover`/`BBDoubling` end-to-end. The
   homotopy obligation is now cheapest via A12's new
   `deckTrivial_of_bezout (P Q) (hPQ : conv P Ac + conv Q Bc = deckPoly)`
   in `BBDoubling.lean` — the S2 matrix's R1 witnesses plug straight in
   (one G-indexed `decide` per instance, kernel-grade, native-free;
   pair72 already retrofitted on the A12 branch). The engine-frame
   flipped presentations (e.g. hit3:anch36 = up to units
   `A ~ 1+x+x²y³`, `B ~ y+y²+x³`) are the natural "second gross"
   engine targets — now with the RIGHT presentations pinned.
4. **A10 coordination — CORRECTED BY A10's L1 (2026-07-02, same day;
   scope fix at A10 note §R6 — cite THAT for Fork-C scope, not this
   note's earlier message).** My message to the A10/Q1 session claimed a
   Fork-C negative "can only be a statement about the stored
   presentations' descent space" — WRONG: A10's Lemma L1 (proven strong
   form, now *constructively demonstrated on hit2/hit5*: transport my
   literal covers back along the Aut-move σ — hit2 σ(e₁,e₂) =
   ((5,3),(5,2)) + translate (3,0), hit5 ((5,3),(5,4)) — and the
   projection σ⁻¹∘π₁ is a MIXED-class (1,1) extension of the STORED
   pair, with twist read off exactly: hit2 (εA=001, εB=010), hit5
   (εA=001, εB=011), matrix equality) makes the 256-cover descent space
   presentation-closed: fixed-presentation screens are code-exhaustive
   over the full Aut × swap × translation orbit. "Literal lift of an
   equivalent presentation" and "twisted descent cover of the stored
   presentation" are two coordinatizations of one phenomenon. A10 also
   independently re-verified both flips (fresh ladders, d = 12 exact).
   Outcome Fork M: hit2/hit5 rescued, but **13 code-level counterexample
   bases** (3× Z₃×Z₃ d=4, 8× Z₃×Z₄ d=4, 2× Z₃×Z₅ d=6; 3328 witness rows
   re-verified, committed on the A10 branch) — and Entry 1's mechanism
   STRENGTHENS them: no equivalent presentation of those 13 doubles
   literally either (any such lift would appear in the screened 256 as
   a rescue row). Two merge items queued with A10: (a) is every rescue
   row in the L1-image of literal lifts of equivalent presentations?
   (b) **C-safe consistency check on the 13 — RUN AND PASSED
   (`a11_s4_thirteen.py`, 13 s)**: all **492** presentation × axis cells
   of the 13 codes (full Aut × swap orbits) have C-safe FALSE, with a
   conjunct-level breakdown of 62 k-drops + 108 missing tight witnesses
   + 322 light safe floors — zero C-safe-true cells, so the criterion is
   consistent with the hardest negative data in the program. (All three
   conjuncts do real work; base list pulled from the A10 branch's
   committed `s3_unrescued_bases.json`.) The safe-sector probe is the
   cheap per-row oracle for A10's selection-rule hunt (pull back
   through L1).
5. **S6 propagation** (after 1–2): promote the surviving criterion into
   `a5_cover_cascade.py` as DOUBLE_CANDIDATE v2 (per-presentation,
   probe-backed), research-log + memory updates, and the A8-note status
   flip from "3 supporting groups" to the new census.

---

## Entry 3 — the Entry-2b hunt FOUND one, and it VERIFIES: first
## observed dangerous-sector bind (2026-07-07)

**Headline.** The 2026-07-02 counterexample-hunt subagent (brief:
`data/a11/cx/BRIEF.md`; scope: weight-4/5 pairs on nine small frames,
the weight-3 world having been screened clean) flagged exactly **one**
counterexample among **2,059 C-safe-true cells** and its session ended
before the brief's mandated from-scratch re-verification. That
re-verification (this session, `scripts/a11_cx_verify_m.py`,
`data/a11/cx/verify_m.json`, 1.7 s) **confirms it on every leg**:

> **(A, B) = (x²y + x³ + x³y³ + x³y⁴, x⁴(1 + y + y² + y⁴))** on
> **Z₅×Z₅** — a [[50,2,5]] code, weights **4×4** — y-axis literal lift
> to Z₅×Z₁₀ = [[100,2,8]]: **C-safe holds (two-sidedly, at enumeration
> grade) yet d(cover) = 8 < 10 = 2·d(base)**, and the failing weight-8
> X-logical pushes to a **weight-6 nonzero stabilizer** — the b ≠ 0
> dangerous rung, binding below 2d for the first time anywhere in the
> program.

**Verification ledger** (independent methods wherever the hunt used the
SAT stack; grades per A_HANDOFF §1):

| leg | result | method / grade |
|---|---|---|
| k(base) = k(cover) = 2 | ✓ | numpy rank (kernel-grade) |
| (R) | ✓ | Bezout `1 + y⁵ ∈ (Ã, B̃)` by colspace rank (A12 theorem; kernel-grade) |
| d(base) ≥ 5, both sides | ✓ | **exhaustive**: all C(50,1..4) = 251,175 supports, zero kernel vectors at all (packed-popcount, no solver) |
| d(base) ≤ 5 | ✓ | SAT witnesses at 5 (X and Z), each re-verified in numpy |
| tight witness | ✓ | translate (0,0) of the weight-5 Z-logical lifts diagonally to a nontrivial weight-10 cover Z-logical (numpy) |
| safe floor, Z side | min = **11** ≥ 10 | **exhaustive** 2²⁴-element stabilizer-coset popcount sweep (replaces the hunt's SAT ladder) |
| safe floor, X side | min = **11** ≥ 10 | same, **new** — closes the honesty-ledger side-gap (the hunt floored only the Z side while its witness is X-type) |
| rank(im p_*) = 1 = k/2, both sides | ✓ | matches Prop A14.1's dim count under (R) |
| weight-8 cover X-logical | ✓ | stored witness: ∈ ker H_Z(cover), ∉ rowspace H_X(cover), weight 8 (pure numpy); fresh from-scratch `x_distance` re-run returns d_X(cover) = 8 (SAT-grade exactness; the counterexample needs only ≤ 8) |
| **sector diagnosis** (never run by the hunt) | **DANGEROUS** | b := p(v) has weight 6, lies in rowspace(H_X base); constructive certificate: **b = the product of exactly two y-adjacent X-checks, cells (1,2) and (1,3)** (Gaussian solve, numpy-reproduced) |
| sheet split | 4 + 4, overlap 1 | \|v\| = \|b\| + 2·overlap = 6 + 2 ✓; v not deck-invariant |

**What this settles.**

1. **"C-safe ⟹ doubling" is FALSE as a weight-agnostic statement.**
   The criterion's three conjuncts — plus (R), plus the X-side floor the
   original criterion never even asked for — all hold at enumeration
   grade, and the cover still under-runs 2d. Sufficiency was never a
   near-theorem lacking only diligence; it genuinely needs a hypothesis
   the even-weight world lacks.
2. **The Entry-2b residue cell is instantiated, exactly.** The bind is a
   light stabilizer b (0 < \|b\| = 6 < 2d) with a fiber logical
   concentrating in its seam shadow: by the D4 accounting, the punctured
   weight is ≤ overlap = 1 < d − \|b\|/2 = 2, i.e. the **D5
   concentration criterion is violated** — the "flux-anomalous light b
   with shadow-concentrating fiber logical" cell, no longer
   hypothetical. The twice-refined residue was the right residue.
3. **Parity is the load-bearing hypothesis, not decoration.** The
   specimen wears the even-weight world's fingerprints: d(base) = 5 is
   ODD and both safe minima are ODD (11) — both impossible under the
   A15-P3 parity lemma L1 (\|A\|, \|B\| odd ⟹ all cycle weights even).
   Also d_safe = 11 > 2d breaks the odd-weight corpus regularity
   "viable cells sit at exactly 2d". The heavy cancellation feeding the
   light b (two adjacent checks collapsing to weight 6) runs through
   B's dense univariate y-support {0,1,2,4} — a shape PAR forbids
   nothing about at even weight.
4. **Consequence for the (M)-robustness conjecture** (deficit-wall §9,
   scoped to corpus-class odd-weight pairs): **not refuted — but now
   non-vacuous and provably scope-critical.** (R) + tight witness +
   two-sided safe floors do NOT imply the dangerous rung; any proof
   must consume \|A\|, \|B\| odd (or what parity buys) in an essential
   way. Within the hunt itself the odd-weight record stays perfect: the
   sole violation is the even×even cell; all-odd and mixed-parity
   C-safe cells doubled without exception (2,058/2,058).
5. **Near-miss context.** The S2 concentration probes (`a11_cx_nearmiss`,
   `a11_cx_exhaustb`) logged 8 relaxed-margin rung dips (Z₃×Z₄, Z₄×Z₆,
   Z₃×Z₅, Z₃×Z₆ — sharpest −4) — relaxation artifacts, none an actual
   bind; the slice probe found 0. The true bind came from S1 random
   sampling. Discovery-vs-guarantee, in miniature.

**Follow-ups queued (cross-session propagation).**

- Fold a scoping footnote into the deficit-wall note §9 (branch
  `claude/charming-euler-ef6879`) at merge: the conjecture's
  corpus-class restriction is *necessary*, witnessed here.
- A15 T4 doctrine ("even w kills PAR — separate study, likely weaker
  floors") now has a doubling-side counterexample, not just a
  floors-side expectation; w = 4 stays deprioritized with sharper
  justification, and the w = 5 lane (all-odd) is unaffected.
- Scope sweep worth one background session: (a) push the 5×5 blocks to
  real sample sizes (all-odd; the conjecture predicts zero binds);
  (b) the mixed-parity 3+4/4+3 C-safe population — one polynomial odd,
  one even — is the sharp boundary of L1's hypothesis and currently
  clean; a bind there would pin exactly *which* parity the proof needs.
- The specimen is the natural model system for proving the odd-weight
  rung: why does oddness forbid a two-check domino with a
  shadow-concentrated fiber logical? (D4/D5 give the quantitative
  target: force punctured weight ≥ d − \|b\|/2.)

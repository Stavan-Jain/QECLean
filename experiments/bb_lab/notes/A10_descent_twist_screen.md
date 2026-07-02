# A10 — Descent-cover twist screen: does every certified BB base admit a distance-doubling free ℤ₂ cover?

**Status: Stage 0 (plan).** Branch `claude/a10-descent-twist-screen`, cut from
the PR #53 head (`292a830`, the parametric doubling layer + the Z3Z6
instance + the A9 screen). This file is the running log for the experiment;
results accrete below the plan, A9-style. Date: 2026-07-02.

---

## 0. TL;DR

**Question.** Given a BB base `(H, A, B)` with certified distance `d`, does
there always exist a *free ℤ₂ cover* — a choice of ℤ₂-extension
`π : G → H` (deck direction) and cover polynomials `(Ã, B̃)` that merely
**descend** (`fiberSumFn π Ã = A`, `fiberSumFn π B̃ = B`) rather than lift
literally — with `d(cover) = 2d`?

**Known.** False when restricted to *literal-lift axis covers*: hit2 and
hit5 (two of gross's five anchorable `[[72,12,6]]` Z₆×Z₆ siblings, A9 §T2)
fail on both axes (hit2 x/y stay at 6; hit5-x reaches only 8), and toric
fails on both axes by symmetry (`d(toric ℤ_a×ℤ_b) = min(a,b)`, so doubling
one axis of a square torus leaves `d = L ≠ 2L`).

**Open.** The full descent space: `2^(w_A+w_B)` sheet-assignment twists per
extension class, times the ℤ₂-extension classes of `H` (both axis classes,
plus the mixed class when both axes are even, plus the split class with
nontrivial voltage — see §2.3 for why the split class is genuinely
in-family).

**Decisive experiment.** Exhaustive twist screen on hit2/hit5 (≤ 256 covers
each, exact SAT verdicts at n = 144). If twists rescue them → evidence for
"always constructible" and a new engine-tier Lean target. If not → strong,
*finitely certifiable* counterexamples: the negative is a per-cover
weight-≤ 11 witness table, checkable by the Lean kernel.

**Why now.** PR #53's `XDoubleCoverData` is *already descent-general*: the
cover polynomials `Ac/Bc` are free fields constrained only by
`push_A/push_B` (the fiberSum equations), and `proj` is any 2:1 hom
(`BBCover.lean:59-85`) — mixed-class and twisted instances need **zero new
Lean framework**. And the verified `[[36,4,4]] → [[72,4,8]]` instance is
itself a split-class cover with nontrivial voltage (`ℤ₆ ≅ ℤ₂×ℤ₃` splits over
the odd axis), so "non-literal" covers already have a fully-proven precedent.

**Epistemic grade.** This is a *screen* (A9 grade): SAT is
discovery/validation only, per the A_HANDOFF §1 constraint. Each fork has
its own certification path (§6): witnesses → Lean kernel for the negative;
template obligations → the parametric layer for the positive.

---

## 1. The question, precisely

Fix a base presentation `(H, A, B)`: `H = ℤ_ℓ × ℤ_m`, `A, B ∈ F₂[H]` of
weights `w_A, w_B` (weight-3 pairs throughout this corpus), with
`d = d(BB(H, A, B))` known exactly (SAT-certified; for hit2/hit5 the base
floor `d ≥ 6` is also analytic via anchorability, A8/A9).

A **group-structured free ℤ₂ descent cover** of `(H, A, B)` is:

- a surjection `π : G → H` of finite abelian groups with `|ker π| = 2`;
  write `δ` for the nonzero kernel element (the deck translation);
- cover polynomials `Ã, B̃ ∈ F₂[G]` with `fiberSumFn π Ã = A` and
  `fiberSumFn π B̃ = B` (each base monomial receives an odd number of its
  two lifts; we restrict to the *weight-preserving* case — exactly one lift
  per monomial — see scoping note §2.4);
- the cover code is `BB(G, Ã, B̃)`: `H̃_X = (M_Ã | M_B̃)`,
  `H̃_Z = (M_B̃ᵀ | M_Ãᵀ)`, `ñ = 2|G| = 2n`.

The **question**: for every certified base, does some such cover satisfy
`k(cover) = k` and `d(cover) = 2d`?

A **literal lift** is the special case: `G` doubles one axis and every
monomial lifts with its exponents unchanged (`x^a y^b ↦ x̃^a ỹ^b`). Both
prior positive instances (gross = x-literal of its base; the Z3Z6 pair) and
all A9 ladder data are literal lifts. The descent space is what the
question actually quantifies over; literal lifts are its zero-twist points.

---

## 2. The search space (per base presentation)

### 2.1 Extension classes — uniform cocycle model

`Ext(ℤ_ℓ×ℤ_m, ℤ₂) ≅ ℤ₂^{[2|ℓ]} × ℤ₂^{[2|m]}`. Implement ALL four classes
`c = (c₁, c₂) ∈ ℤ₂²` uniformly as cocycle extensions on the set
`ℤ₂ × ℤ_ℓ × ℤ_m`:

```
(s,a,b) + (s',a',b') = (s + s' + c₁·carry_ℓ(a,a') + c₂·carry_m(b,b'),
                        a+a' mod ℓ,  b+b' mod m)
```

with `carry_ℓ(a,a') = 1` iff `a+a' ≥ ℓ`. Then `π(s,a,b) = (a,b)`,
`δ = (1,0,0)`, `sec(a,b) = (0,a,b)`, and every fiber is
`{(0,a,b), (1,a,b)}` — literally the `XDoubleCoverData` field list
(`proj_fiber`, `proj_sec` hold by construction).

- `c = (1,0)`: the x-axis cover (`G ≅ ℤ_{2ℓ}×ℤ_m` when 2∤ℓ this is
  iso to the split group but presented as the x-double — same code space
  as the classical "double the x period" cover);
- `c = (0,1)`: the y-axis cover;
- `c = (1,1)`: the **mixed class** — genuinely new when both `ℓ, m` even
  (for Z₆×Z₆: `G ≅ ℤ₁₂×ℤ₆` abstractly but with the diagonal projection —
  NOT equivalent-over-id_H to either axis cover);
- `c = (0,0)`: the **split class**. With zero voltage this is two disjoint
  base copies (`d(cover) = d`, auto-fail — kept as an enumeration sanity
  row). With nontrivial voltage it is a genuine connected free cover.

### 2.2 Twists (voltage / sheet assignment)

For a fixed class, a twist is `ε = (ε_A, ε_B) ∈ F₂^{w_A} × F₂^{w_B}`: the
i-th monomial `x^{a_i} y^{b_i}` of `A` lifts to `(ε_A[i], a_i, b_i)`, same
for `B`. Weight preserved, `fiberSum` descent automatic (distinct base
monomials have disjoint fibers). For weight-3 pairs: `2^6 = 64` twists per
class, `4 × 64 = 256` covers per base. The literal lift of an axis cover is
a specific twist point in this parametrization (the lift of `x^a y^b` into
the cocycle model has `s = ` the carry-accumulated bit of `a` resp. `b`;
compute it, don't assume `ε = 0` — validated by the S1 matrix-equality
test against A9's `cover_group`/`lift_poly` construction).

### 2.3 Why the split class belongs

The verified `[[36,4,4]] → [[72,4,8]]` instance doubles the ODD axis of
`ℤ₃×ℤ₆` (deck `(3,0)`): the extension `ℤ₆ → ℤ₃` is split as groups, so in
the classification above the instance sits in the split-with-voltage
sector. Free-ness and the whole `XDoubleCoverData` apparatus are
class-agnostic; excluding `c = (0,0)` for even-even bases would make the
even-even screen *less* general than the machinery we already trust. Cost:
64 extra covers per base. (The user-posed space is the three nonzero
classes; the split column is a completeness appendix and its rows are
flagged separately in the census.)

### 2.4 Scoping decisions (fixed for A10)

1. **Weight-preserving lifts only.** `fiberSum` also allows inflating `Ã`
   by canceling pairs `{g, g+δ}` — that changes the row weight (LDPC-ness)
   and opens an infinite space. Out of scope; note in the writeup.
2. **`k(cover) = k` required for "rescue".** The census records `k(cover)`
   for every candidate regardless (rank drift under twists is possible and
   interesting), but only `k`-preserving covers count toward the question.
3. **Group-structured covers only.** General free ℤ₂ covers of the Tanner
   graph (per-edge voltages up to gauge, `H¹(Tanner, ℤ₂)`) form a vastly
   larger space that destroys the BB form. A negative here is a
   counterexample for *BB-structured* descent covers — state the theorem
   with that scope.
4. **Presentation exhaustiveness (Lemma L1, to nail down in S1).** A9's
   caveat — doubling is presentation-sensitive — is resolved at the
   descent level: if `σ ∈ Aut(H)` carries `(A,B)` to an equivalent
   presentation `(A^σ, B^σ)`, then `σ` lifts to an isomorphism of the
   class-`c` extension onto the class-`c∘σ` extension carrying twist
   spaces bijectively and inducing cover-code equivalences. Since the
   screen ranges over ALL classes and ALL twists, the fixed-presentation
   space already covers the code-level descent space up to equivalence.
   Deliverable: short proof sketch in this file + machine validation
   (random `σ`, compare `canonical_pair` forms of the matched covers —
   `bb_lab/canonical.py:230`).
5. **Gauge is reporting-only.** Known cover equivalences — joint
   translation `(Ã,B̃) → (δÃ, δB̃)`, generator re-sectioning
   (`x̃ → x̃+δ` shifts `ε` by the exponent-parity pattern) — quotient the
   256 raw covers to fewer classes. The screen runs the RAW space
   (exhaustiveness must not depend on a gauge lemma); orbits are computed
   empirically for the census statistics.

---

## 3. Prior evidence (what the screen must reproduce before it says anything new)

| base | cover | verdict | source |
|---|---|---|---|
| gross base `[[72,12,6]]` (A=x³+y+y², B=y³+x+x²) | x-literal | d = 12 ✓ doubles | gross itself; A3/A4 analytic |
| Z3Z6 `[[36,4,4]]` (A=x²+y+y³, B=1+x+y²) | x-literal, deck (3,0) | d = 8 ✓ doubles | PR #53, Lean-proven |
| hit3 (A=y³+x+x², B=y+x·y²+x²) | y-literal | d = 12 ✓ doubles | A9 T2 ladders |
| hit4 (B=y²+x·y³+x²·y), hit6 (B=x·y+x²·y²+x³) | y-literal | d = 12 ✓ | A9 T2 addendum |
| **hit2** | x- and y-literal | **d stays 6** ✗ | A9 T2 |
| **hit5** | x-literal | **d = 8** ✗ (y: see regenerated JSON) | A9 T2 |
| toric ℤ_L×ℤ_L (A=1+x, B=1+y) | either axis literal | d = L ✗ | symmetry (min-axis distance) |
| 152 T1 pairs (n ≤ 96 frames) | axis literals | doubling ✓ | A9 T1 hunt |

hit2/hit5's exact `B` polynomials live in `data/a9/t2_presentation_hits.json`,
which was never committed — S0 regenerates it from the corpus duckdb
(`a9_lean_target_screen.py t2` is the fast subcommand). All five hits share
`A = y³+x+x²` up to equivalence-normalization.

---

## 4. Stages

### S0 — recover ground truth (cheap, this session or next)

- Copy/point at the corpus: `data/bb_instances.duckdb` exists in the main
  repo checkout (read-only per lab rules); the worktree needs a symlink or
  `--db` path.
- `uv run python scripts/a9_lean_target_screen.py t2` → regenerate
  `t2_presentation_hits.json`; pin hit2/hit5 `(A, B)` exactly, record them
  in this file.
- Re-run the hit2/hit5 literal ladders (4 covers, n = 144, SAT cap 12) to
  reproduce the A9 verdicts (6/6/8/?) — this is the harness-independent
  baseline the twist screen must match at its zero-twist points.

### S1 — the descent-cover harness (`scripts/a10_descent_covers.py` + tests)

New module functions (reuse `bb_lab.{poly,linalg,sat_distance,checks,canonical}`):

- `CocycleGroup(ell, m, c1, c2)` — the §2.1 model: element indexing
  `(s,a,b) ↦ s·ℓm + a·m + b`, addition, negation, and a generic
  group-algebra matrix builder `M_P[g,h] = P[g − h]` matching the lab's
  circulant convention (validated against `bb_check_matrices` on the
  trivial group cases).
- `twisted_lift(P, group, eps)` — §2.2.
- `descent_cover_checks(base, c, eps) -> CheckMatrices` for the cover code.
- `enumerate_covers(base)` — the 256 rows.

**Tests (all must pass before any screen result is quoted):**

1. Class `(1,0)`/`(0,1)` zero-twist covers reproduce A9's
   `cover_group`+`lift_poly` matrices exactly (up to the documented index
   map — make it equality, not just code-equivalence).
2. Control distances: Z3Z6 doc-verified pair x-literal → `d = 8` exact
   (k = 4); toric L=3 axis-literal → `d = 3`; gross-base x-literal →
   `d = 12` (one n = 144 ladder — the expensive control, run once).
3. `fiberSum` descent holds for random twists (numpy re-implementation,
   independent of the builder).
4. BB-form duality `d_X = d_Z` spot-checked on twisted covers (compute
   both on 20 random small covers); if it holds — as the transpose
   symmetry argument predicts for any `(G, Ã, B̃)` in BB form — the screen
   computes one side only.
5. Lemma-L1 validation: random `σ ∈ Aut(H)`, matched covers
   `canonical_pair`-equivalent.

### S2 — toric warm-up (cheap, decisive for the symmetry-failure family)

Full 256-cover screens on toric L=3 (n_cover = 36) and L=4 (n_cover = 64,
all four classes live). Exact distances throughout (SAT is instant here).
Output: does ANY descent cover of a square torus reach `2L`? This is the
cheapest direct test of "twists rescue symmetric failures" and an
independent data point regardless of the hit2/hit5 outcome. (Note the
mixed-class covers of toric are close cousins of the twisted-toric
`ℤ²/Λ` codes — see `project_twisted_toric_scoping`; don't conflate the
two uses of "twist".)

### S3 — small-frame rescue-rate sweep (the statistics arm)

From the A9 hunt corpus (T1_FRAMES, n_cover ≤ 96): select the bases whose
axis-literal covers FAILED to double (the complement of the 152 pairs in
the hunt stream — the hunt JSONL records `d(cover)` per candidate, and is
regenerable). Budget-capped (~50 bases): run the full 256-cover descent
screen per base, exact SAT (cheap at this size). Outputs:

- **rescue rate**: fraction of literal-failures rescued by some twist;
- twist-position statistics of rescuers (do rescuing twists concentrate
  on particular classes / voltage patterns? — the raw material for any
  future selection rule or obstruction conjecture);
- per-base `max_d over descent space` distribution.

This arm turns the binary hit2/hit5 answer into a trend line, and
battle-tests the harness before the expensive runs.

### S4 — the decisive runs: hit2 and hit5 exhaustive (n = 144)

Per base, 256 covers, fail-fast pipeline per cover:

1. `k` via `rank_f2` (instant). Record; skip to census if `k ≠ 12`.
2. Witness ladder: `x_distance(..., weight_upper_bound = 11)` — SAT hit at
   `w ≤ 11` kills the cover cheaply (most twists die here, low `w`);
   record the witness vector (this IS the counterexample certificate).
3. Survivors (`UNSAT through 11`): confirm `d = 12` exactly with a SAT
   call at 12, then re-run the UNSAT ladder with `proof_dir` set (LRAT
   emission) for the archival certificate.
4. Optional per-survivor: A9 `profile_pair`-style template obligations
   (R-homotopy, linchpin, safe-class minima, tight witness) — is a rescue
   also *template-provable*?

Artifacts: `data/a10/{hit2,hit5}_descent_screen.jsonl` (append-per-cover,
resumable, A9-hunt style) + a census table in this file.

Cost model: A9's hunt did ~640 SAT ladders at n ≤ 96 in 30–90 min; the
n = 144 UNSAT-through-11 ladders were done for 10 covers in the T2 pass.
Here most of the 512 covers die at low weight (cheap SATs); expect hours,
one machine, no Lean, no workspace lock. Run the two bases sequentially,
JSONL-resumable.

### S5 — interpretation + certification (fork-dependent, see §5–§6)

### S6 — writeup: A10 results section in this file, A_HANDOFF pointer
update, extensibility-doc §8 delta, research_log entry. Promote any new
generalizable pattern per the pipeline's Stage-6 reflection recipe.

---

## 5. Outcome forks

**Fork R (rescued): some twist of hit2 and/or hit5 reaches exact d = 12.**
Evidence for "always constructible". Follow-ups, in order:
(a) S3's rescue statistics become the main exhibit — is the rescue rate
100% across all literal-failures?; (b) hunt a *selection rule* (which
class/voltage rescues, and why — the seam-flux and difference-set
predicates from A5/A8 are candidate explanatory variables); (c) the
rescued cover joins hit3-y as an engine-tier Lean target: Z₆×Z₆ bases have
36 cells, out of direct-sweep reach, so full certification needs the
CRT/F₄ engine re-instantiation (A9 §T2) — the near-term Lean-certified
claim is the template-obligation profile, not `d = 12`; (d) pose the
general conjecture with the correct quantifier ("for every certified BB
base there is a descent cover with d(cover) = 2d") and look for the
constructive mechanism.

**Fork C (counterexample): every one of the 256 covers of hit2 (resp.
hit5) has k ≠ 12 or a weight-≤ 11 logical.**
Then hit2/hit5 are counterexamples over the FULL group-structured descent
space — much stronger than the literal-lift failures. This is *finitely
certifiable*: the negative is a table of ≤ 256 witnesses per base, each
checkable by kernel `decide` (logical-operator membership + weight at
n = 144 is a trivial check; no sweeps). Package as a Lean theorem
("no free ℤ₂ BB-descent cover of hit2 doubles its distance", quantifying
over the four cocycle classes × 64 twists), scope-qualified per §2.4(3)
and backed by Lemma L1 for the code-level reading. Update the
extensibility doc: the doubling mechanism is genuinely *conditional* — the
frame-correlation story (in-frame ⟹ heavy safe ⟹ doubling) gains its
first certified negative instances on the engine frame itself.

**Fork M (mixed): one rescued, one not.** Both packages above, one per
base; "always constructible" is falsified either way by the negative one,
while the positive one still feeds Fork R's mechanism hunt.

---

## 6. Certification paths (why both forks are Lean-ready)

- **Layer generality (verified on-branch):** `XDoubleCoverData` fields
  `proj/deckS/sec/Ac/Bc` + `proj_fiber/proj_sec/push_A/push_B`
  (`BBCover.lean:59-85`) are satisfied by every §2.1–2.2 cover — the
  cocycle model IS the bundle. Twisted/mixed instances re-use
  `BBDoubling.lean` theorems unchanged; only the four finite obligations
  are per-instance.
- **Negative fork:** witness table + `decide`-grade checks; no
  `native_decide`, no sweeps, no engine. The cheapest certification in
  the whole program.
- **Positive fork:** template obligations via the layer; full `d = 12`
  needs the engine re-instantiation (same status as hit3-y, which remains
  the queued engine target — a rescued twist cover would join, not jump,
  that queue).

---

## 7. Risks and traps (read A_HANDOFF §6 first)

1. **Hand-rolled CNF is guilty until sanity-laddered.** The screen only
   uses `bb_lab.sat_distance` (validated, reproduces d(gross) = 12), never
   a fresh encoding. Any new helper must reproduce the S1 controls before
   its output is quoted.
2. **Literal-lift ≠ zero-twist in the cocycle model** (carry bits). The S1
   matrix-equality test exists precisely to kill this off-by-one.
3. **Presentation trap** (A9's caveat): resolved by Lemma L1 + screening
   all classes; do not quote a code-level negative before L1 is written
   down and machine-validated.
4. **k drift**: a twisted cover with `k ≠ 12` is not a rescue even if its
   distance is large; the pipeline computes `k` first.
5. **Duality shortcut**: computing only `d_X` is valid only after the S1
   test-4 spot-check; if any twisted cover breaks `d_X = d_Z`, compute
   both sides for all candidates (double SAT cost, still feasible).
6. **Solver asymmetry** (memory: UNSAT intractable at n ≥ 288): n = 144 is
   inside the feasible envelope (A9 did UNSAT@11 there), but if a survivor
   ladder stalls, fall back to recording `d ≥ w_stalled` and escalate only
   the decisive bit (`≥ 12` vs `= 12`).
7. **No Lean builds in the screen loop** — the whole experiment is
   Python + SAT; the workspace lock is never touched. Lean work starts
   only in S5, in its own session, sequentially with any Y-floor builds
   (~8 GB each, per PR #53 notes).
8. **data/ hygiene**: `data/*.duckdb` read-only; all A10 outputs under
   `data/a10/` (JSONL, append-only, resumable); nothing under `data/` is
   committed unless small and load-bearing (the witness tables are — they
   are the certificates).

---

## 8. Definition of done

- [ ] S0: hit2/hit5 polynomials pinned in this file; literal baselines
      reproduced.
- [ ] S1: harness + 5 test classes green (`uv run pytest` includes them).
- [ ] S2: toric L∈{3,4} full screens; verdict recorded.
- [ ] S3: ≥ 30 literal-failure bases screened; rescue rate + twist
      statistics tabulated.
- [ ] S4: hit2 and hit5 exhaustive screens complete with per-cover
      verdicts; survivors (if any) LRAT-certified; witnesses archived.
- [ ] S5: fork identified; certification artifact started (Lean witness
      theorem for Fork C, or template profile + conjecture memo for
      Fork R).
- [ ] S6: writeup + handoff/extensibility/research-log updates.

The headline question this experiment answers: **"is distance-doubling by
free ℤ₂ covering an *intrinsic* capability of certified BB bases, or a
special property of some (frame-correlated) subfamily?"** — with hit2/hit5
as the decisive instances either way.

---
---

# RESULTS (accreting below; plan above is frozen)

## R0. Stage S0 — ground truth recovered (2026-07-02)

`scripts/a10_s0_recover_hits.py` reproduces the A9 T2 pass exactly from
the corpus duckdb: 326 Z₆×Z₆ k>0 d≥6 codes → **6 presentation-anchorable
→ 6 canonical classes** (~25 s for the Aut×swap search).  Labels, pinned
by the published polynomials (hit3/4/6, gross base) and by the ladder
signature for the rest (hit5 = the one whose x-literal reaches 8):

| label | instance_id | A | B | literal x/y cover d |
|---|---|---|---|---|
| gross_base | `5620b8e2c34acc75` | y³+x+x² | 1+x·y²+x²·y | (gross itself: 12) |
| hit2 | `98ff6753f866aba0` | y³+x+x² | 1+x·y⁵+x²·y | **6 / 6** |
| hit3 | `9b9581f986a0d0ac` | y³+x+x² | y+x·y²+x² | (y: 12, A9) |
| hit4 | `8b3fe87db2da2b48` | y³+x+x² | y²+x·y³+x²·y | (y: 12, A9) |
| hit5 | `9706a4ea60d7e978` | y³+x+x² | y⁵+x·y+x² | **8 / 6** |
| hit6 | `702393fa5fd7449c` | y³+x+x² | x·y+x²·y²+x³ | (y: 12, A9) |

New datum: **hit5-y = 6** (A9 recorded only hit5-x = 8).  Regenerated
artifacts: `data/a9/t2_presentation_hits.json`,
`data/a9/t2_cover_ladders.json`.  Ladder cost at n = 144 is far below
the plan's estimate: **sub-second per non-doubling ladder**; the gross
d = 12 control (UNSAT through 11) runs in **88 s** — the per-survivor
cost calibration for S4.

## R1. Stage S1 — harness green

`scripts/a10_descent_covers.py` + `tests/test_a10_descent_covers.py`:
43 fast tests + the slow gross control, all passing.  Notables:

- The plan's §2.2 worry about literal-lift ≠ zero-twist was wrong in a
  pleasant direction: under the iso `(s,a,b) ↦ (a+ℓs, b)` the zero
  twist IS the literal lift, verified by exact matrix equality against
  the a9 `cover_group`/`lift_poly` builder on both axis classes.
- The inversion duality `d_X = d_Z` holds on twisted covers (§docstring
  proof: `M_Pᵀ = M_{ι(P)}`, `ι` a ring automorphism — group- and
  twist-agnostic); numerically spot-checked.  The screen computes `d_X`
  only.
- Lemma-L1 consequence test: the full-descent-space `(k, d)` multiset is
  Aut(H)-presentation-invariant (toric L=3, two random automorphisms).
- Controls: Z3Z6 doc-verified pair x-literal → d = 8 exact, k = 4;
  toric L=3 x-literal → d = 3; gross-base x-literal → d = 12 exact.

## R2. Stage S2 — toric warm-up: TWISTS RESCUE THE TORUS

Full 256-cover screens (`data/a10/toric{3,4}_descent_screen.jsonl`),
exact SAT throughout.

**L = 3 ([[18,2,3]], odd×odd):** 16/64 non-split-degenerate covers
rescue (d = 6 = 2L, k = 2), 4 per class — every class carries rescuers:

| class | rescuing twists (εA; εB) |
|---|---|
| x | εA constant, εB non-constant |
| y | εA non-constant, εB constant |
| mixed | both constant |
| split | both non-constant |

The pattern is exactly a **holonomy rule**: with `A = 1+x`, `B = 1+y`,
the cover doubles iff both fundamental directions of the torus have
nontrivial ℤ₂ holonomy, where the x-holonomy = c₁ (class carry) +
L·Δε_B-ish twist contribution (odd L ⟹ a non-constant twist on the
transverse polynomial flips the holonomy).  These rescued covers are
the **twisted-toric ℤ²/Λ codes** (Λ an index-2L² non-rectangular
sublattice) — the classical d ~ optimal twisted torus, recovered by the
descent screen with zero geometry-specific input.

**L = 4 ([[32,2,4]], even×even):** the parity wall — on an even axis
the twist holonomy `L·Δε = 0 (mod 2)` vanishes, so **x/y-class covers
all fail (32/32) regardless of twist**; the **split class never
doubles** (16/16 k-drop); but the **mixed class rescues with ALL 16
twists** (d = 8 = 2L, k = 2): its holonomy is intrinsic (both carries),
so twists cannot cancel it (they only shift by even amounts).

**Toric verdict: always constructible — but on even×even frames ONLY
via the mixed extension class.**  This is the first structural signal
for hit2/hit5: they live on Z₆×Z₆ (even×even).  Unlike toric, weight-3
BB polynomials generate odd-length relative cycles too, so axis twists
are not automatically impotent there — but the toric result already
justifies the plan's §2.1 insistence on the mixed class.

## R2.5 Lemma L1 — proven (stronger than planned)

**Lemma L1.** Fix `H` and a base pair `(A, B)`; let `σ ∈ Aut(H)`.  The
descent covers of `(A^σ, B^σ)` are the SAME cover codes as those of
`(A, B)`, with extension classes permuted by `σ`: if `π : G → H` has
class `c` and `fiberSumFn π Ã = A`, then `π' := σ∘π : G → H` has class
`σ_*(c)` and `fiberSumFn π' Ã = A^σ` — the cover code `BB(G, Ã, B̃)`
is *literally unchanged*; only which base presentation it covers (and
along which projection) is re-indexed.

*Proof.* `fiberSum_{π'}(Ã)(h) = Σ_{π(g)=σ⁻¹(h)} Ã(g) = A(σ⁻¹h) =
A^σ(h)`; `ker π' = ker π = ⟨δ⟩`, and the Ext-class of `σ∘π` is the
image of `c` under `Ext(σ⁻¹, id)`. □

Two consequences.  (i) **Code-level exhaustiveness**: since the screen
ranges over ALL four classes, the union of its cover codes is invariant
across the whole `Aut(H)`-orbit of base presentations — the A9
presentation-sensitivity caveat does not apply to descent screens.
(A9's literal-lift hunts were the zero-twist SLICE of this space, and a
slice is presentation-sensitive; the full space is not.)  Block swap
and pair translation are absorbed the same way (`(Ã,B̃) ↦ (B̃,Ã)` /
`(g̃Ã, g̃B̃)`).  My §2.1 cocycle models represent every class up to an
iso over `id_H`, which carries descent pairs to descent pairs and
induces code equivalences.  (ii) **Within a fixed presentation** the
only twist-space gauge is the joint deck flip
`(Ã,B̃) ↦ (δÃ, δB̃)` (all `w_A + w_B` bits flip), so the 64 twists per
class fall into ≤ 32 equivalence pairs; the raw screen double-covers
this, harmlessly.  Machine validation: the verdict-profile invariance
test (`test_l1_presentation_invariance`) passes.

## R3. Stage S3 (interim) — NOT always constructible: small-frame counterexamples

Early census (first 33 complete bases, Z₃×Z₃ + Z₃×Z₄, all d_base = 4,
k = 4): 9 double literally; **13 literal-failures are twist-rescued —
all on Z₃×Z₄, all rescued exclusively by the y/mixed classes** (the
even y-axis needs its holonomy from the class carry, exactly the toric
parity lesson); and **11 literal-failures are NOT rescued by ANY of
their 256 descent covers** (8 on Z₃×Z₄, 3 on Z₃×Z₃ — the latter on an
all-odd frame where every twist direction is live).  Their whole
descent space tops out at d = 6 < 8 = 2d.

Each unrescued base is a complete, finitely-certified (SAT-witness
grade) counterexample: **the A10 question's universal form is FALSE.**
The refined question — which certified bases admit descent doubling —
is now a selection-rule hunt, with the hit2 rescue (R4) showing the
answer is not "literal-lift-equivalent" either.

**Certificate verification:** every row of the unrescued bases'
descent spaces re-verifies independently
(`scripts/a10_verify_certificates.py`: rebuild each cover from
`(base, class, twist)` alone, recompute `k` by rank, re-check each
witness's kernel membership / logical pairing / rowspan exclusion /
weight in pure numpy — no SAT): **3328/3328 rows PASS** (2992
witnessed fails + 336 k-drops) at the first snapshot.  Committed as
`data/a10/s3_unrescued_certificates.jsonl` +
`s3_unrescued_bases.json` (the `data/` tree is gitignored; these are
force-added — the A9 data-loss lesson).

**Selection-rule leads (snapshot, hypotheses only):**

- On the 41-base Z₃×Z₃/Z₃×Z₄ d=4 stratum, `is_sidon(B)` separated
  perfectly: every unrescued base had Sidon (repeat-free difference
  set) `B`, every rescued/literal base non-Sidon `B`.  The clean-
  difference-structure codes — the ones the analytic floor machinery
  likes — are the descent-resistant ones there.
- The rule does NOT survive richer strata: two `d = 6` bases on
  Z₃×Z₅ (`0558ff082fa2ec09`, `09d82cd19d904915`, A = y+x+x²) are
  unrescued with **non-Sidon** B (max descent d = 8 < 12); and
  hit2/hit5 have **Sidon** B yet are rescued on Z₆×Z₆ (R4).  Sidon-ness
  is a minimal-frame obstruction pattern, not the mechanism.
- On Z₃×Z₄ every rescue goes through the y/mixed classes (the even
  axis needs its holonomy from the class carry — the toric parity
  lesson); the x/split classes rescue nothing on that frame.

## R4. Stage S4 — THE DECISIVE ANSWER: hit2 AND hit5 are both rescued

Both gross siblings that fail every literal-lift axis cover admit
exact-doubling descent covers, `k = 12` preserved, `d = 12 = 2·6`
SAT-exact (UNSAT through 11 + weight-12 witness):

- **hit2** (`98ff6753f866aba0`, B = 1+x·y⁵+x²·y): rescued in the
  x-class by single-bit twists — first confirmed `(εA, εB) =
  (000, 001)` (twist the x²y monomial of B onto the other sheet), and
  by `(000,011), (000,100), (000,110), (001,000)` (a twist on A alone
  also works), plus mixed-class rescuers `(000,010), (000,011)`, …
- **hit5** (`9706a4ea60d7e978`, B = y⁵+x·y+x²): rescued by the **mixed
  class at zero twist** — the pure mixed ℤ₂-extension, exactly the
  toric even×even pattern — plus mixed `(000,{011,100,111})` and
  x-class `(000,{001,011})`, …

(The per-class 64-twist grids are still filling in as the four workers
grind — each rescue confirmation is an UNSAT@11 at n = 144, ~2–7 min.
Refresh with `uv run python scripts/a10_census.py`; the JSONLs under
`data/a10/hit{2,5}_descent_screen*.jsonl` are append-resumable.)

**Archival certificates** (`scripts/a10_s5_certify.py`, cadical CLI):
one representative rescue per base re-run with per-weight DRAT proof
emission and an independent numpy witness verification —

- `data/a10/certs/hit2_c10_eA000_eB001/certificate.json`: n=144, k=12,
  d=12, witness verified, UNSAT proofs w=1..11 (605 s).
- `data/a10/certs/hit5_c11_eA000_eB000/certificate.json`: same shape.

The DRAT files are ~1–2 GB per cover and stay local (regenerable);
the certificate JSONs are committed.

So the A9 verdict "hit2 and hit5 do not double" was a statement about
the literal-lift slice *at the stored presentation*, and it flips under
a single sheet-assignment bit (or, for hit5, under the mixed extension
class with no twist at all).  **All five anchorable [[72,12,6]]
siblings of the gross base now have exact [[144,12,12]] covers** —
hit3/4/6 literally (A9), hit2/hit5 by descent (A10).  *(See R6 for the
A11 cross-session synthesis: these rescues and the literal covers of
equivalent presentations are the same codes in different coordinates —
"strictly enlarges the literal slice at this presentation", not
"strictly enlarges presentation-closed literal lifting".)*

## R5. Fork determination: Fork M, with a sharp two-level structure

- **Globally: NOT always constructible.**  13 complete counterexample
  bases so far (3 × Z₃×Z₃ d=4, 8 × Z₃×Z₄ d=4, 2 × Z₃×Z₅ d=6), each
  with all 256 descent covers failing, witnessed, and independently
  re-verified.  The two Z₃×Z₅ d=6 counterexamples are all-odd-frame
  and non-Sidon — no known structural excuse.
- **On the engine frame: constructible everywhere tested.**  All five
  gross siblings double.  Whether Z₆×Z₆ certified bases are ALWAYS
  descent-doublable is the sharpened open question the S3 trend line
  (and a future Z₆×Z₆-targeted sweep) should answer.

The refined research object is the **selection rule**: what property
of `(H, A, B)` decides descent-doublability?  Live leads: the
Sidon(B) pattern (minimal frames only), the even-axis class-carry
requirement, and the frame-richness effect (Z₆ = ℤ₂×ℤ₃ gives twists
odd-component leverage that ℤ₄ denies them).

## R6. A11 cross-session synthesis: twists ≡ presentation moves (2026-07-02)

The A11 session (`claude/a8-literal-lift-criterion`, note
`A11_literal_lift_criterion.md` Entry 1) reported: the A9 T2 ladders
ran on the STORED corpus presentations, which fail the anchorability
gate (iii); the ANCHORABLE presentations of hit2/hit5 (e.g. hit2:
A = 1+x+x²y³, B = y²+x³+x³y) have **literal x-covers with d = 12
exactly** — so literal-lift doubling is presentation-sensitive within
one (code, axis), and all six anchorable Z₆×Z₆ classes are gross-twins.
Their positive claim **verifies independently** here (fresh ladders,
`blxtkaey7` run: both anchorable literal x-covers d = 12, k = 12).

**Synthesis via Lemma L1 (constructive).**  A11's finding and this
screen's rescues are the same phenomenon in different coordinates.
`scripts/a10_l1_correspondence.py` computes the presentation move
(σ, translation) carrying the stored pair to the anchorable pair,
transports the anchorable literal x-cover back along σ, classifies the
resulting extension, builds the explicit iso ψ onto the cocycle model,
and reads off the twist bits:

- hit2: anchorable-literal-x  ≡  stored-presentation **mixed-class
  (εA=001, εB=010)** — *exact matrix equality* under ψ;
- hit5: anchorable-literal-x  ≡  stored-presentation **mixed-class
  (εA=001, εB=011)** — exact matrix equality.

So the anchorable presentations' literal covers ARE rows of this
screen (as L1 requires: the x-class of a moved presentation pulls back
to a different class of the stored one — here mixed — with a computable
twist).  The mixed-class zero-twist rescuer of hit5 found earlier is a
*further* rescuer beyond that image.

**Correction to the A11 message's consequence (1).**  A11 inferred "a
Fork-C negative can only be a statement about the stored
presentations' descent space, not about the codes."  L1 says the
opposite, and the correspondence above demonstrates it on the exact
contested instance: descent-cover codes are invariant under
presentation moves (§R2.5 — the cover code is literally unchanged,
only (class, twist) bookkeeping moves), so a fixed-presentation screen
over ALL FOUR classes is code-level exhaustive.  Consequently the R3
counterexamples are strengthened, not weakened, by A11's mechanism:
for each of the 13 unrescued bases, **no equivalent presentation
(Aut × swap × translation orbit) admits a doubling literal lift
either** — any such lift would appear in the screened 256 as a rescue
row.  What IS presentation-relative (A11 is right here) is any claim
about the *literal-lift slice alone*, including A9's T2 ladder
verdicts and this note's earlier "strictly enlarges" phrasing (fixed
in R4).

**Net effect on framing:** the descent screen is the
presentation-invariant closure of literal-lift search — it subsumes
presentation search (a 576-element orbit hunt) at the cost of a 256-row
screen, and its negatives are code-level.  A11's safe-sector coset
diagnostics (stored-x minima {6:12, 8:45, ≥12:6} vs anchorable-x
{≥12:63}, base-side probe, no cover SAT) are exactly the cheap
per-(class, twist) predictor the R5 selection-rule hunt wants — pulled
back through the L1 correspondence they become a per-row screen
oracle.  Open follow-up (now sharper): are ALL rescue rows in the
L1-image of {literal lifts of equivalent presentations}, or does the
descent space rescue codes that NO presentation rescues literally?
The 576×2 move-image is directly computable per base; run it against
the finished hit2/hit5 grids.

## R8. The L1-image analysis: DESCENT STRICTLY BEATS PRESENTATION-CLOSED LITERAL LIFTING (2026-07-02)

R6's open question is answered.  `scripts/a10_l1_image.py` computes,
purely group-theoretically (no SAT), the **presentation-literal
L1-image** of a screen: the set of rows (class, epsA, epsB) that are
L1-transports of literal axis covers of ANY moved presentation
(Aut × swap × translation), including the full row-level gauge
(deck-lift choice, and all consistent trivializing cochains η — note:
η's generator values are pinned by the cocycle data, an early-version
bug; and on frames with odd axes several cocycle models are
equivalent-over-id_H, so image rows are emitted in every model whose
η exists).

Results against the grids:

| base | image size | rescues in-image / descent-proper (screened so far) |
|---|---|---|
| toric3 (complete) | 32/64 (8 per model) | 8 / **8** |
| toric4 (complete) | 24/64 (x,y,mixed only) | 8 / **8** (all mixed) |
| hit2 (partial) | **192/256 — saturates all three nonsplit classes** | 11 / 0 (forced: only split-class rows can be outside) |
| hit5 (partial) | **96/256 — half of each nonsplit class** | 6 / **7** |

**Headline: hit5 has confirmed d = 12, k = 12 doubling covers that are
literal lifts of NO equivalent presentation.**  The three x-class
descent-proper rescues — (εA, εB) = (000,001), (000,011), (001,000) —
were re-verified at a *stronger* grade by
`scripts/a10_l1_image_verify.py`: mapped onto Z₁₂×Z₆, a pair is
equivalent to a literal lift iff some Aut(Z₁₂×Z₆)-image fits in a
width-6 x-window with windowed reduction among the 10368 moved
presentations (set membership, no canonicalization).  The literal
control row tests IN; all three descent-proper rows test OUT — i.e.
outside the literal image **even under full Aut(Z₁₂×Z₆) × swap ×
translation**, strictly broader than the group-structured gauge.
(The four mixed-class descent-proper rows rest on the row-level
gauge-complete image; their canonical-grade re-check via an abstract
iso mixed → Z₁₂×Z₆ is queued.)

Consequences:

1.  The descent space is *strictly* larger than presentation-closed
    literal lifting — sheet twists are a genuinely new construction
    axis, not presentation search in disguise.  (A11's mechanism
    explains SOME rescues — hit5's zero-twist mixed rescue and all of
    hit2's nonsplit rescues are in-image — but not all.)
2.  The image size is itself a sharp per-code invariant and new
    selection-rule variable: hit2 saturates its nonsplit classes
    (192/256) while hit5 fills only half (96/256) — the two siblings
    differ structurally in how much of their descent space literal
    lifting can reach.
3.  Even toric already separates: half its rescuing covers (both L)
    are descent-proper — the skew-torus covers reachable by twists
    but not by axis-doubling any GL-transformed square-torus
    presentation.

## R7. Follow-ups (queued)

1. **Lean instance of a rescued cover** — `XDoubleCoverData` verifies
   descent-generality by construction (R2.5 / plan §6); hit2's
   `(x, 000, 001)` cover is statement-ready, but its `d = 12` proof is
   engine-tier (36-cell base): joins hit3-y in the engine-target queue.
   The four finite template obligations should first be profiled on the
   rescued covers (adapt `a9.profile_pair` to cocycle covers).
2. **Fork-C Lean packaging for a small counterexample** — e.g.
   `b78e8b27ffa1fef2` (Z₃×Z₃, [[18,4,4]], descent space = 256 covers,
   all witnessed ≤ 6): "no free ℤ₂ BB-descent cover doubles this code"
   as a kernel-`decide` theorem over the witness table.  Cheapest
   full-rigor artifact of the program; would make the FALSE side of
   the A10 question axiom-clean.
3. **Complete the S3 sweep** (Z₃×Z₅/Z₃×Z₆/Z₄×Z₆ strata) and re-run the
   discriminator analysis on the full sample.
4. **Z₆×Z₆ d≥6 targeted sweep** (the 326-code corpus): is the engine
   frame universally descent-doublable?
5. **Gauge-quotient reporting** and the holonomy invariant: formalize
   the per-relative-cycle ℤ₂ holonomy that explains the toric grids and
   test it as a rescue predictor on the BB data.
